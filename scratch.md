What are (locally-small) categories?


a category consists of 'arrows'

arrows are programs

an arrow is denoted `f ∷ A ▷ B`

the `A ▷ B` bit is a type

the `f` is a term in that type

the labels `A` and `B` are called 'objects'

objects aren't necessarily types, e.g:

1. where `List ▷ Maybe` is the type `∀ i . List i → Maybe i`

2. where `0 ▷ 1` is the type `0 ≤ 1`

3. where `<a,b> ▷ <s,t>` is the type `Lens s t a b`

to know what type `A ▷ B` is, we need to know what category we're using

for every object `I` there is an identity arrow: `id ∷ I ▷ I`

any two compatible arrows can be composed

compatible means that equal objects line up

so, given `f ∷ A ▷ B` and `g ∷ X ▷ A`

because the two `A`s can line up,

we can have the composition `f ∘ g ∷ X ▷ B`

this composition is always a function `(∘) ∷ (A ▷ B) → (X ▷ A) → (X ▷ B)`



the following laws must hold (for some suitable notion of equivalence `≅`)

1. Left Identity: `(id ∘ f) ≅ f`

2. Right Identity: `f ≅ (f ∘ id)`

3. Associativity: `((f ∘ g) ∘ h) ≅ (f ∘ (g ∘ h))`



there is a category called `TYPE` in which

* objects are proper types, e.g: `Int`, `String`

* arrow types are function types, e.g: `Int ▷ String` is `Int → String`

composition is regular function composition

each identity arrow is the identity function



functors map from one category to another

a functor `F` from a category `C` to a category `D`

maps objects `A` of `C` to objects `F A` of `D`

maps arrows `q ∷ A ▷ B` in `C`

to an arrow `F q ∷ F A ▷ F B` in `D`

think of the `F q` bit in a similar way to `fmap q`



for any category `C` and any object `X`, it turns out that

the partially-applied arrow type `X ▷ ?` is a functor from `C` to `TYPE`

it maps `C`-objects `B` to `TYPE`-objects `(X ▷ ?) B`, which is the type `X ▷ B`

it maps `C`-arrows `f ∷ A ▷ B` to `TYPE`-arrows `(X ▷ ?) f ∷ (X ▷ A) ▷ (X ▷ B)`

which is the function `(X ▷ ?) f ∷ (X ▷ A) → (X ▷ B)`

this mapping on arrows is actually partially applied composition:

`(X ▷ ?) : (A ▷ B) → (X ▷ A) → (X ▷ B)`

`(X ▷ ?) = (∘)`

