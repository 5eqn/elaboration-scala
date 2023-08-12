# elaboration-scala

[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) partially rewritten with Scala3.

## If you want a full version...

See [The Commented](./src/main/scala/commented/Elaboration.scala)! This is a fully-commented version of the latest chapter, `fcpoly.polyarg`.

## Comment Logic

In each file, important differences from the previous one are commented.

For example, in `implicit.insert`, `Elaboration.scala` is the only file that has comment, which means the other files remain unchanged relative to the previous chapter `implicit.model`.

## Major Differences

- Difficulty curve of mine is not as steep as the original
    - The original project implements Holes in one go, but I separated it to four parts
    - There's a variety of tests running the code from different aspects
        - You can even see de-Bruijn indexes in tests
        - Parser is also implemented in Scala3
- I made less documentation and references, for that please refer to the original
- I try to write idiomatic Scala3 code instead of solely adhering to the original
    - Using Singleton when implementing Meta is much more convenient
- I added chapters that I enjoy but not necessarily relate to typechecking
    - e.g. Pretty Exceptions

## Fun Facts

This project is rewritten from memory, when something goes wrong, I refer to original elaboration-zoo to spot the mistake. Here are some mistakes that I've made (and of course fixed):

- As `let b = a; ?` can't be `b`, there's no need for assigning a de-bruijn index to `b`, but I mistakenly assigned one when writting tests
- When inferring type of `Pi x a b`, I forgot to make sure `b : U`
- When inferring type of `Let x a t u`, I forgot to make sure `a: t`
- I made sure when `(\_ => ?) : A -> ?`, `A : U`, elaboration-zoo didn't check that (because type itself is already typechecked?)
- did not fresh a new name in `conv`
- did not check eta conversion
- In `(x : A) -> ?`, `A` can't include `x`, but I mistakenly assigned a de-bruijn index when writting tests
- When generating `Term` in bidirectional elaboration, I made the context wrong in `Let` and `Lam`.
- I forgot to force some values when implementing holes
- I ignored the fact that let-bound variables exist in `env` as complicated objects, partial renaming shouldn't fail on these
- I forgot to update the solved meta to memory (literally)
- I forgot to check if lhs and rhs are both meta first in `unify`
- I forgot to enable checking type of lambdas
- I forgot to insert implicit arguments when checking type of implicit function against explicit Pi type
- I forgot to make sure name of inserted variable doesn't collide with existing ones
- I forgot to recurse insert function
- When implementing spine comparison, I mistakenly use `foldRight`
- When generating lambdas, I mistakenly use `foldRight`
    - I made detailed explanation on these two `foldLeft`s
- When inferring type of function application, when the function's type is meta, I forgot to attempt to unify it with `?0 -> ?1`
    - However, no tests will fail without this
- Getting type of `Val` *makes no sense*, so there's no need storing a `types` array in `Ctx`
- I didn't recurse `force`!
- I forgot to reverse spine when pretty printing
- I used `ctx.bind` instead of `ctx.define` when pretty-printing `let`

Here are some of my unclear points:

- In elaboration-zoo 02, `check` checks `Let` separately, is this necessary?
    - Current tests all pass, btw
- In elaboration-zoo 05, `invert` doesn't prune all nonlinear arguments, it keeps the first occurrence. Is this intended?
    - I plan to read more materials about pruning later, but currently I'll just keep this as a question

## Run Tests

Simply run:

```sh
sbt test
```

You can also change the test sources to see failed cases! Also note that there're built-in tests on failed cases in later chapters.

## Difficulty Order

Personal ratings are decided by deltas, i.e. the difficulty of `norm.closure.names` means how hard it is to understand `norm.closure.names` *after* learning `norm.hoas.names`, not the overall difficulty. That's why you'll see some latter parts have less difficulty compared to former parts.

More stars, more difficult. Difficulty no more than 5* is acceptable.

1. Normalization
    1. norm.hoas.names (3*)
    2. norm.closure.names (2*)
    3. norm.closure.debruijn (4*)
2. MLTT Typecheck
    1. typecheck.hoas.names (4*)
    2. typecheck.closure.names (1*)
    3. typecheck.closure.debruijn (3*)
3. Holes
    1. holes.assemble (1*)
    2. holes.spine (3*)
    3. holes.renaming (4*)
    4. holes.meta (5*)
    5. holes.filter (3*)
4. Implicit Arguments
    1. implicit.modularize (1*)
    2. implicit.model (3*)
    3. implicit.insert (5*)
    4. implicit.named (3*)
    5. implicit.catch (3*)
    6. implicit.filter (1*)
5. Pruning
    1. prune.typed (4*)
    2. prune.scope (5*)
    3. prune.nonlinear (4*)
    4. prune.intersect (3*)
6. First-Class Poly
    1. fcpoly.tylam (3*)
    2. fcpoly.defer (5*)
    3. fcpoly.block (4*)
    4. fcpoly.polyarg (3*)

## Benchmarks

### AddingBench

```
sbt:elaboration-scala3> Jmh/run -i 3 -wi 3 -f1 -t1 .*Adding.*
```

```
[info] Result "benchmark.AddingBench.measureRight":
[info]   1.162 ±(99.9%) 0.105 ns/op [Average]
[info]   (min, avg, max) = (1.157, 1.162, 1.169), stdev = 0.006
[info]   CI (99.9%): [1.057, 1.267] (assumes normal distribution)
```

### PruneTyBench

The test code calls pruneTy over a Pi chain with 16 parameters:

```
sbt:elaboration-scala3> Jmh/run -i 3 -wi 3 -f1 -t1 .*PruneTy.*
```

A tail-recursive implementation referring to original elaboration-zoo:

```
[info] Result "benchmark.PruneTyBench.elabZoo":
[info]   910.837 ±(99.9%) 232.661 ns/op [Average]
[info]   (min, avg, max) = (896.217, 910.837, 919.669), stdev = 12.753
[info]   CI (99.9%): [678.176, 1143.498] (assumes normal distribution)
```

My alternative implementation of pruneTy using less-readable anonymous function, this implementation is about 25% faster, potentially due to lack of optimization for tail-recursing in JVM:

```
[info] Result "benchmark.PruneTyBench.elabScala":
[info]   678.676 ±(99.9%) 56.736 ns/op [Average]
[info]   (min, avg, max) = (675.942, 678.676, 682.059), stdev = 3.110
[info]   CI (99.9%): [621.940, 735.412] (assumes normal distribution)
```

### PruneVFlexBench

The test code calls pruneVFlex over a Val.Flex with 16 parameters:

```
sbt:elaboration-scala3> Jmh/run -i 3 -wi 3 -f1 -t1 .*PruneVFlex.*
```

A pure-functional version adhering to the original haskell implementation:

```
[info] Result "benchmark.PruneVFlexBench.elabZoo":
[info]   1478.936 ±(99.9%) 62.369 ns/op [Average]
[info]   (min, avg, max) = (1476.244, 1478.936, 1482.782), stdev = 3.419
[info]   CI (99.9%): [1416.566, 1541.305] (assumes normal distribution)
```

A more-readable version utilizing mutable variables, there's no evident performance gain from this, but I prefer this implementation:

```
[info] Result "benchmark.PruneVFlexBench.elabScala":
[info]   1412.891 ±(99.9%) 171.762 ns/op [Average]
[info]   (min, avg, max) = (1407.358, 1412.891, 1423.761), stdev = 9.415
[info]   CI (99.9%): [1241.129, 1584.652] (assumes normal distribution)
```

## Contribution

As I'm a beginner, I make mistakes. If you found one, submitting Issue or Pull Request is greatly welcomed!
