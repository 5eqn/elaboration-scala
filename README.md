# elaboration-scala

[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) partially rewritten with Scala3.

## Fun fact

This project is rewritten from memory, when something goes wrong, I refer to original elaboration-zoo to spot the mistake. Here are some mistakes that I've made (and of course fixed):

- As `let b = a; ?` can't be `b`, there's no need for assigning a de-bruijn index to `b`, but I mistakenly assigned one when writting tests
- When inferring type of `Pi x a b`, I forgot to make sure `b : U`
- When inferring type of `Let x a t u`, I forgot to make sure `a: t`
- I made sure when `(\_ => ?) : A -> ?`, `A : U`, elaboration-zoo didn't check that (because type itself is already typechecked?)

Here are some of my unclear points:

- In elaboration-zoo, `check` checks `Let` separately, is this necessary?

## Run Tests

Simply run:

```sh
sbt test
```

## Difficulty Order

1. norm
    1. norm.hoas.name
    2. norm.closure.name
    3. norm.closure.debruijn
