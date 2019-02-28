{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language TypeInType #-}
{-# Language UnicodeSyntax #-}
module Main where

-- a (locally small) category consists of 'arrows'
-- arrows are programs
-- an arrow is denoted `f ∷ A ▷ B`
-- the `A ▷ B` bit is a type
-- the `f` is a term in that type
-- the labels `A` and `B` are called 'objects'
-- objects aren't necessarily types, e.g:
-- 1. where `List ▷ Maybe` is the type `∀ i . List i → Maybe i`
-- 2. where `0 ▷ 1` is the type `0 ≤ 1`
-- 3. where `<a,b> ▷ <s,t>` is the type `Lens s t a b`
-- to know what type `A ▷ B` is, we need to know what category we're using

-- any two compatible arrows can be composed
-- compatible means that equal objects line up
-- so, given `f ∷ A ▷ B` and `g ∷ X ▷ A`
-- because the two `A`s can line up,
-- we can have the composition `f ∘ g ∷ X ▷ B`
-- this composition is always a function `(∘) ∷ (A ▷ B) → (X ▷ A) → (X ▷ B)`
-- which function `(∘)` denotes, depends on which category is involved

-- for every object `I` there is an identity arrow: `id ∷ I ▷ I`

-- the following laws must hold (for some suitable notion of equivalence `≅`)
-- 1. Left Identity: `(id ∘ f) ≅ f`
-- 2. Right Identity: `f ≅ (f ∘ id)`
-- 3. Associativity: `((f ∘ g) ∘ h) ≅ (f ∘ (g ∘ h))`

-- there is a category called `TYPE` in which
-- * objects are proper types, e.g: `Bool`, `Int`
-- * arrow types are function types, e.g: `Bool ▷ Int` is `Bool → Int`
-- composition is regular function composition
-- each identity arrow is the identity function

-- (∘) ∷ ∀ a b x . (a ▷ b) → (x ▷ a) → (x ▷ b)
compose_TYPE ∷ ∀ a b x . (a → b) → (x → a) → (x → b)
compose_TYPE ab xa x = ab (xa x)
-- this is associative and has the following identities
-- id Bool ∷ Bool ▷ Bool
-- id Int ∷ Int ▷ Int
-- ...
id_TYPE ∷ ∀ i . i → i
id_TYPE i = i


-- A monoid is a category with exactly one object, say `♣`.
-- The only arrow type is `♣ ▷ ♣`.
-- Therefore all the arrows are composable.
-- The arrows are referred to as the elements or members of the monoid.
-- composition `(∘)` is called append `(<>)`
-- identity is called mempty

-- suppose our arrow type `♣ ▷ ♣` is `ALL`
type ALL = Bool
-- thus, the only arrows/elements are `True` and `False`
-- with composition/append as `&&`
-- (∘) ∷ (♣ ▷ ♣) → (♣ ▷ ♣) → (♣ ▷ ♣)
compose_ALL ∷ ALL → ALL → ALL
compose_ALL l r = l && r
-- the associativity of `∘` follows from that of `&&`
-- and the identity/mempty for this composition is `True`
-- id ∷ ♣ ▷ ♣
identity_ALL ∷ ALL
identity_ALL = True


-- We can construct a monoid from an existing category by picking one object and
-- it's arrows, and forgetting about everything else.
-- If we do this with the `TYPE` category; pick an object, e.g `Int`.
-- Regard all the arrows `f ∷ Int ▷ Int` as elements of the monoid `f ∷ ♣`.
-- Then, append follows from composition of the original category;
-- and mempty follows from the identity.
type ENDO_INT = Int → Int
-- (<>) ∷ ♣ → ♣ → ♣
compose_ENDO_INT ∷ ENDO_INT → ENDO_INT → ENDO_INT
compose_ENDO_INT l r = compose_TYPE l r
-- mempty ∷ ♣
id_ENDO_INT ∷ ENDO_INT
id_ENDO_INT = id_TYPE

-- We can clearly generalise this in haskell by allowing the user to pick which
-- object they care about.
type ENDO i = i → i
-- (<>) ∷ ♣ → ♣ → ♣
compose_ENDO ∷ ∀ i . ENDO i → ENDO i → ENDO i
compose_ENDO l r = compose_TYPE l r
-- mempty ∷ ♣
id_ENDO ∷ ∀ i . ENDO i
id_ENDO = id_TYPE


-- Another monoid that we probably already know is lists with `(++)` and `[]`
compose_LIST ∷ ∀ i . [i] → [i] → [i]
compose_LIST l r = l ++ r
id_LIST ∷ ∀ i . [i]
id_LIST = []


-- We can construct a new category by combining two existing categories.
-- One such construction is a cross-product.
-- Suppose we are constructing the cross-product of `TYPE` and `ENDO i`.
-- Which we will call `TYPE×ENDO i`.
-- An object of `TYPE×ENDO i` is one object from `TYPE` and one from `ENDO i`,
-- for example `<Int, ♣>` - remember `ENDO i` only has one object (`♣`)
-- An arrow of `TYPE×ENDO i` is is arrow from `TYPE` and one from `ENDO i` such
-- that the objects are taken pair-wise as follows:
-- Given `f ∷ Int ▷ String` (in `TYPE`) and `g ∷ ♣` (in `ENDO i`)
-- We have the arrow `<f, g> ∷ <Int, ♣> ▷ <String, ♣>`
-- This could be modelled in haskell with `(TYPExENDO i) Int String`:
-- We don't mention objects of `ENDO i` as type arguments
-- because there's only one argument.
type (TYPExENDO i) d c = (d → c, ENDO i)
-- composition pairwise delegates to the underlying categories
-- <∘, <>> ∷ ∀ a b x . (<a, ♣> ▷ <b, ♣>) → (<x, ♣> ▷ <a, ♣>) → (<x, ♣> ▷ <b, ♣>)
compose_TYPExENDO ∷ ∀ i a b x .
  (TYPExENDO i) a b → (TYPExENDO i) x a → (TYPExENDO i) x b
compose_TYPExENDO (ab, l) (xa, r) =
  (compose_TYPE ab xa, compose_ENDO l r)
-- as is identity:
-- <id, mempty> ∷ ∀ x . <x, ♣> ▷ <x, ♣>
id_TYPExENDO ∷ ∀ i x . (TYPExENDO i) x x
id_TYPExENDO = (id_TYPE, id_ENDO)


-- ---


-- functors map from one category to another
-- a functor `F` from a category `C` to a category `D`
-- maps objects `A` of `C` to objects `F A` of `D`
-- maps arrows `q ∷ A ▷ B` in `C`
-- to an arrow `F q ∷ F A ▷ F B` in `D`
-- think of the `F q` bit in a similar way to `fmap q`

-- for any category `C` and any object `X`, it turns out that
-- the partially-applied arrow type `X ▷ ?` is a functor from `C` to `TYPE`
-- it maps `C`-objects `B` to `TYPE`-objects `(X ▷ ?) B`, which is the type `X ▷ B`
-- it maps `C`-arrows `f ∷ A ▷ B` to `TYPE`-arrows `(X ▷ ?) f ∷ (X ▷ A) ▷ (X ▷ B)`
-- which is the function `(X ▷ ?) f ∷ (X ▷ A) → (X ▷ B)`
-- this mapping on arrows is actually partially applied composition:
-- `(X ▷ ?) : (A ▷ B) → (X ▷ A) → (X ▷ B)`
-- `(X ▷ ?) = (∘)`

