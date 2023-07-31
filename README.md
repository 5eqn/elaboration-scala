# elaboration-scala

[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) partially rewritten with Scala3.

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
- I made certain implementation simpler
    - In metas, I didn't filter defined variables
    - In implicit, I use "?" prefix instead of env masking to ensure variable names don't collide
    - I didn't allow implicit lambda generating, where `a : A, b : B, a b` gets elaborated to `(\_. a) b`
- I try to write idiomatic Scala3 code instead of solely adhering to the original
    - Using Singleton when implementing Meta is much more convenient

## Fun fact

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
- When implementing spine comparison, I mistakenly use foldRight

Here are some of my unclear points:

- In elaboration-zoo, `check` checks `Let` separately, is this necessary?
    - Current tests all pass, btw

## Run Tests

Simply run:

```sh
sbt test
```

You can also change the test sources to see failed cases!

## Difficulty Order

Personal ratings are decided by deltas, i.e. the difficulty of `norm.closure.names` means how hard it is to understand `norm.closure.names` **after** learning `norm.hoas.names`, not the overall difficulty. That's why you'll see some latter parts have less difficulty compared to former parts.

More stars, more difficult. Difficulty no more than 5* is acceptable.

1. norm
    1. norm.hoas.names (3*)
    2. norm.closure.names (2*)
    3. norm.closure.debruijn (4*)
2. typecheck
    1. typecheck.hoas.names (4*)
    2. typecheck.closure.names (1*)
    3. typecheck.closure.debruijn (3*)
3. holes
    1. holes.assemble (1*)
    2. holes.spine (3*)
    3. holes.renaming (4*)
    4. holes.meta (5*)
4. implicit
    1. implicit.modularize (1*)
    2. implicit.model (3*)
    3. implicit.insert (5*)
    4. implicit.named (3*)

## Contribution

As I'm a beginner, I make mistakes. If you found one, submitting Issue or Pull Request is greatly welcomed!
