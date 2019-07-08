# [ringal](https://github.com/eschnett/ringal)

Experiment with Semiringal and Ringal type classes, extending
Semigroupal and Monoidal.

* [GitHub](https://github.com/eschnett/ringal): Source
  code repository
* TODO:
  [Hackage](http://hackage.haskell.org/package/ringal):
  Haskell package and documentation
* TODO:
  [Stackage](https://www.stackage.org/package/ringal):
  Stackage snapshots
* [Azure
  Pipelines](https://dev.azure.com/schnetter/ringal/_build):
  Build Status [![Build
  Status](https://dev.azure.com/schnetter/ringal/_apis/build/status/eschnett.ringal?branchName=master)](https://dev.azure.com/schnetter/ringal/_build/latest?definitionId=1&branchName=master)



## `TheseList` is `Semiringal`

`TheseList` is based on `Data.These`. It is similar to `ZipList`,
except that it can naturally handle lists of uneven lengths:

```Haskell
newtype TheseList a = TL [a]

(<+>) :: TheseList a -> TheseList b -> TheseList (These a b)
TL (x:xs) <+> TL (y:ys) = TL (These x y : rs)   where TL rs = TL xs <+> TL ys
TL (x:xs) <+> TL [] = TL (This x : rs)          where TL rs = TL xs <+> TL []
TL [] <+> TL (y:ys) = TL (That y : rs)          where TL rs = TL [] <+> TL ys
TL _ <+> TL _ = TL []
```

`TheseList` can also be combined with the "usual" `Applicative`
instance via `(<*>)`:

```Haskell
(<+>) :: TheseList a -> TheseList b -> TheseList (a, b)
TL xs <*> TL ys = TL [(x, y) | x <- xs, y <- ys]
```

As it turns out, `(<+>)` distributes over `(<*>)`. Also, the empty
list is the neutral element for `(<+>)`, and is an absorbing element
for `(<*>)`. These are the conditions for a semiring! Hence,
`TheseList` is semiringal.

This is also witnessed by the lengths of the lists:

```Haskell
length (xs <+> ys) = length xs + length ys
length (xs <*> ys) = length xs * length ys
```



## Related Work

* [A tale on
  Semirings](https://lukajcb.github.io/blog/functional/2018/11/02/a-tale-of-semirings.html)
* [Compiling to
  categories](http://conal.net/papers/compiling-to-categories/)
* [Monoidal Functor is Applicative but where is the Monoid typeclass
  in the definition of
  Applicative?](https://stackoverflow.com/questions/50702929/monoidal-functor-is-applicative-but-where-is-the-monoid-typeclass-in-the-definit/50717675#50717675)
* [The Functor
  Combinatorpedia](https://blog.jle.im/entry/functor-combinatorpedia.html)
* [Type Classes: Semiring](https://typeclasses.com/semiring)
* [Wikipedia: Monoidal
  functor](https://en.wikipedia.org/wiki/Monoidal_functor)
* [Wikipedia: Ring](https://en.wikipedia.org/wiki/Ring_(mathematics))
* [Wikipedia: Semigroup](https://en.wikipedia.org/wiki/Semigroup)
* [Wikipedia: Tropical
  semiring](https://en.wikipedia.org/wiki/Tropical_semiring)
