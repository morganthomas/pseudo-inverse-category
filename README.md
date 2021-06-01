# pseudo-inverse-category

A pseudo-inverse category is a category in which all morphisms have pseudo inverses. The notion of a pseudo inverse of a morphism is a generalization of the notion of an inverse of a morphism.

An _inverse_ of a morphism `f` is a morphism `g` such that `g . f = id` and `f . g = id`. We say that a morphism is _invertible_ when it has an inverse. With the concept of a pseudo-inverse, we relax these requirements. If `f :: a -> b` is a morphism and `g :: b -> a` is its pseudo-inverse, then `f . g :: b -> b` and `g . f :: a -> a` are not necessarily the identity morphisms, but composition of a morphism with its pseudo-inverse obeys algebraic laws involving additional operations on morphisms that are only defined in a pseudo-inverse category.

In a pseudo-inverse category, every morphism has a pseudo-inverse. Each pseudo-inverse category `a` has the following operations defined on morphisms:

```Haskell
pipower :: Int -> a x y -> a x y
pileft :: a x y -> a x x
piright :: a x y -> a y y
piinverse :: a x y -> a y x
```

Here `a` is like `->`; that is, `a x y` is the type of morphisms from `x` to `y`.

`piinverse` maps a morphism to its pseudo-inverse.

`pileft` maps a morphism to an endomorphism of its domain. Similarly, `piright` maps a morphism to an endomorphism of its codomain. If `f`'s pseudo-inverse is an inverse, then `pileft f = id` and `piright = id`. Otherwise, `pileft f` and `piright f` may be general endomorphisms (non-identity morphisms).

`pipower` applies a morphism repeatedly. In a normal category, the notion of applying a morphism repeatedly only makes sense for endomorphisms. In a pseudo-inverse category, we can define the notion for all morphisms. The following pseudo-inverse category laws can be construed as a recursive definition of the power operation for `n >= 1`:

```Haskell
pipower 1 f = f
pipower (n+1) f = pileft f . pipower n f
```

In other words, `pipower` repeatedly applies the domain endomorphism of `f` before applying `f`.

We can also look at the dual of this power operation, which repeatedly applies the codomain endomorphism of `f` after applying `f`. This dual does not need its own definition because we can write it as `piinverse (pipower n (piinverse f))`.

Pseudo-inverse categories obey various laws which are documented in the comments in `Control.PseudoInverseCategory` on the definition of `PseudoInverseCategory`.

Although pseudo-inverse categories are categories, the usual notion of Arrow does not readily apply to pseudo-inverse categories. For this reason we define a new typeclass, `PIArrow`, such that if a pseudo-inverse category `a` instantiates `PIArrow a` then it is a category of pseudo-invertible arrows. This typeclass defines essentially the same operations as `Arrow`, except that it does not include `arr`. `arr` can't be expected to be definable on pseudo-inverse categories because it turns a function into an arrow, but an arbitrary function provides no way to get a pseudo-inverse. Instead of `arr`, `PIArrow` includes two methods, `piiso`, which creates an arrow from an isomorphism, and `piendo`, which creates an arrow from an endomorphism.

The motivating example of a `PseudoInverseCategory` is `EndoIso`. You can think of an `EndoIso` morphism as a composition of an endomorphism with an isomorphism. `EndoIso` satisfies the following typeclasses:

```Haskell
instance Category EndoIso
instance Control.Categorical.Functor EndoIso (->) Identity
instance ToHask EndoIso
instance HasHaskFunctors EndoIso
instance PseudoInverseCategory EndoIso
instance PIArrow EndoIso
```

Let's go through these one by one.

 * `EndoIso` is a category.
 * There is a [functor](https://hackage.haskell.org/package/category-0.2.5.0/docs/Control-Categorical-Functor.html) from `EndoIso` to `(->)` where the action on objects is `Identity`. `Control.Categorical.Functor` (in the package `category`, as opposed to the package `categories` which contains a very similar module of the same name) defines the general notion of functors between two categories where the objects are Haskell types. This is distinct from `Functor`s, which are endofunctors in the category `Hask` where the objects are Haskell types and the morphisms are Haskell functions. Because all categories in Haskell have as objects all Haskell types, the only difference between two categories in Haskell is the morphisms. For instance, the morphisms can be functions, as in the category `(->)`, or they can be `EndoIso`s, as in the category `EndoIso`. A `Control.Categorical.Functor` instance describes how to map the objects (in this case via the `Identity` functor) and how to map the morphisms. In this case we have a functor from `EndoIso` to `(->)`, and the map on morphisms simply strips away the pseudo-inverse to get the underlying function.
 * There is an `instance ToHask EndoIso` to encode the fact that there is a functor from `EndoIso` to `Hask`. In other words this instance is essentially a restatement of the fact stated by `instance Control.Categorical.Functor EndoIso (->) Identity`. However it is stated in a more conveniently usable form with the `ToHask` instance, and this form of the statement factors into the `PIArrow` laws.
 * There is an `instance HasHaskFunctors EndoIso` to express the fact that all endofunctors of `Hask` can be mapped to endofunctors of `EndoIso` in a way which constitutes a functor from the monoidal category of endofunctors of `Hask` to the monoidal category of endofunctors of `EndoIso`.
 * There are instances `PseudoInverseCategory EndoIso` and `PIArrow EndoIso` to express the fact that `EndoIso` is a pseudo-inverse category of arrows.

In addition, `Control.PseudoInverseCategory` contains this instance:

```Haskell
instance Applicative m => Control.Categorical.Functor EndoIso EndoIso (Continuation m)
```

This instance relates to [Shpadoinkle](http://shpadoinkle.org/) continuations. It expresses that for each `Applicative m`, `Continuation m` is an endofunctor of `EndoIso`. This statement is in fact the motivating fact for all of the concepts in this package. The question which motivated this package is, do Shpadoinkle continuations constitute functors? The answer is yes, but they do not constitute a `Functor`; that is, they are not endofunctors of `Hask`. Rather, Shpadoinkle continuations constitute endofunctors of the `EndoIso` category.

Let's look at why this is the case. Why are Shpadoinkle continuations not endofunctors of `Hask`? To be a `Functor`, or in other words an endofunctor of `Hask`, a type constructor `f :: * -> *` must allow for an operation `fmap :: (a -> b) -> (f a -> f b)` which maps any morphism in `Hask` to a morphism in `Hask`. It is not possible to define `fmap` for Shpadoinkle continuations.

Why is it not possible to define `fmap` for Shpadoinkle continuations? To change the type of a continuation, i.e. to go from `Continuation m a` to `Continuation m b`, we require a lens. In other words we require a setter function `a -> b -> b` and a getter function `b -> a`. These are in other words the inputs to `liftC` which yield a function `Continuation m a -> Continuation m b`. A morphism in `Hask`, i.e. a function `a -> b`, is not enough to change the type of a continuation because it only tells us how to go one way and not how to go back in the other direction. 

An `EndoIso` contains enough information to change the type of a continuation. An `EndoIso` consists of an endomorphism and an isomorphism. We can change an isomorphism from `a` to `b` to an isomorphism from `Continuation m a` to `Continuation m b` using `contIso` defined in `Shpadoinkle.Continuation`. We can change an endomorphism of `a` to an endomorphism of `Continuation m a` using the following function: `Continuation f . const . pure`. In other words, given a function `f :: a -> a` and a continuation `g :: Continuation m a`, we obtain a `Continuation m a` by prepending the pure updating function `f` to the continuation `g`. By combining these two methods, one for changing the type of a continuation using an isomorphism and one for changing the type of a continuation using an endomorphism, we obtain the definition of `map` for the `Control.Categorical.Functor` instance for `Continuation m`, which is an endofunctor over the category `EndoIso`.

Finally, `Control.PseudoInverseCategory` contains these instances:

```Haskell
instance Applicative m => Control.Categorical.Functor EndoIso EndoIso (Html m)
instance Applicative m => Control.Categorical.Functor EndoIso EndoIso (Prop m)
instance Applicative m => Control.Categorical.Functor EndoIso EndoIso (Props m)
```

These instances say that `Html m`, `Prop m`, and `Props m` are also (like `Continuation m`) endofunctors of the `EndoIso` category for any `Applicative m`. These can be viewed as corollaries of the similar functor instance for `Continuation m`. To change the type of an `Html m` or a `Prop m` or a `Props m` means to change the view model type which the event handlers assume. In other words it means to change the type of the continuations which the event handlers produce.
