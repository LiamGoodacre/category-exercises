{-# Language DerivingStrategies #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language InstanceSigs #-}
{-# Language RankNTypes #-}
{-# Language UnicodeSyntax #-}
module Main where

-- a (locally small) category consists of 'arrows'
-- an arrow is denoted `f ∷ A ▷ B`
-- the `A ▷ B` bit is a type
-- the `f` is a term in that type
-- the labels `A` and `B` are called 'objects'
-- objects aren't necessarily types of kind `Type`, e.g:
-- 1. `List ▷ Maybe` could be the type `∀ i . List i → Maybe i`, where `List` and `Maybe` have kind `Type → Type`
-- 2. `0 ▷ 1` could be the type `0 ≤ 1`, where `0` and `1` are natural numbers
-- 3. `<a,b> ▷ <s,t>` could be the type `Lens s t a b`, where `<a,b>` and `<s,t>` are pairs of types
-- to know what type `A ▷ B` is, we need to know what category we're using

-- any two compatible arrows can be composed
-- compatible means that "equal" objects line up
-- so, given `f ∷ A ▷ B` and `g ∷ X ▷ A`
-- because the two `A`s can line up,
-- we can have the composition `f ∘ g ∷ X ▷ B`
-- this composition is always a function `(∘) ∷ (A ▷ B) → (X ▷ A) → (X ▷ B)`
-- which function `(∘)` denotes, also depends on which category is involved

-- for every object `I` there is an identity arrow: `id ∷ I ▷ I`

-- the following laws must hold (for some suitable notion of equivalence `≅`)
-- 1. Left Identity: `(id ∘ f) ≅ f`
-- 2. Right Identity: `f ≅ (f ∘ id)`
-- 3. Associativity: `((f ∘ g) ∘ h) ≅ (f ∘ (g ∘ h))`

-- there is a category called `TYPE` in which
-- * objects are proper types, e.g: `Bool`, `Int` (things of kind `Type`)
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
-- The arrows are referred to as the "elements" or "members" of the monoid.
-- composition `(∘)` is called append `(<>)`
-- identity `id` is called `mempty`
-- To capture this idea, Haskell has a type class called `Monoid`

-- consider the monoid of booleans under `&&`
-- the elements of the monoid are `True` and `False`
-- this means our arrow type `♣ ▷ ♣` is equivalent to `Bool`
-- let's make a newtype for this - so we have `ALL = ♣ ▷ ♣`
newtype ALL = All Bool
  deriving newtype Show
-- composition/append is `&&`
-- (∘) ∷ (♣ ▷ ♣) → (♣ ▷ ♣) → (♣ ▷ ♣)
compose_ALL ∷ ALL → ALL → ALL
compose_ALL (All l) (All r) = All (l && r)
-- the associativity of `∘` follows from that of `&&`
-- and the identity/mempty for this composition is `True`
-- id ∷ ♣ ▷ ♣
id_ALL ∷ ALL
id_ALL = All True
-- we can use these definitions to declare a Monoid instance:
instance Semigroup ALL where
  (<>) = compose_ALL
instance Monoid ALL where
  mempty = id_ALL


-- We can construct a monoid from an existing category by picking one object and
-- all the arrows that start and end at that object - forgetting about everything else.
-- If we do this with the `TYPE` category; pick an object, e.g `Int`.
-- Regard all the arrows `f ∷ Int ▷ Int` as elements of the monoid.
-- Then, append follows from composition of the original category;
-- and mempty follows from the identity.
newtype ENDO_INT = EndoInt (Int → Int)
-- (<>) ∷ (Int ▷ Int) → (Int ▷ Int) → (Int ▷ Int)
compose_ENDO_INT ∷ ENDO_INT → ENDO_INT → ENDO_INT
compose_ENDO_INT (EndoInt l) (EndoInt r) = EndoInt (compose_TYPE l r)
-- mempty ∷ (Int ▷ Int)
id_ENDO_INT ∷ ENDO_INT
id_ENDO_INT = EndoInt id_TYPE
instance Semigroup ENDO_INT where
  (<>) = compose_ENDO_INT
instance Monoid ENDO_INT where
  mempty = id_ENDO_INT


-- We can clearly generalise this in Haskell by allowing the user to pick which
-- object from `TYPE` that they care about.
newtype ENDO i = Endo (i → i)
-- (<>) ∷ ∀ i . (i ▷ i) → (i ▷ i) → (i ▷ i)
compose_ENDO ∷ ∀ i . ENDO i → ENDO i → ENDO i
compose_ENDO (Endo l) (Endo r) = Endo (compose_TYPE l r)
-- mempty ∷ ∀ i . (i ▷ i)
id_ENDO ∷ ∀ i . ENDO i
id_ENDO = Endo id_TYPE
instance Semigroup (ENDO i) where
  (<>) = compose_ENDO
instance Monoid (ENDO i) where
  mempty = id_ENDO


-- Another monoid that you perhaps already know of is lists with `(++)` and `[]`.
-- Remember, there's a single object `♣` in this category.
-- In this case the arrow type `(♣ ▷ ♣)` is the type `[i]`
-- i.e lists of `i`s, for some type `i`.
-- (<>) ∷ (♣ ▷ ♣) → (♣ ▷ ♣) → (♣ ▷ ♣)
compose_LIST ∷ ∀ i . [i] → [i] → [i]
compose_LIST l r = l ++ r
-- mempty ∷ (♣ ▷ ♣)
id_LIST ∷ ∀ i . [i]
id_LIST = []


-- We can construct a new category by combining two existing categories.
-- One such construction is a cross-product.
-- Suppose we are constructing the cross-product of `TYPE` and `ENDO i`.
-- Which we will call `TYPE×ENDO i`.
-- An object of `TYPE×ENDO i` is one object from `TYPE` and one from `ENDO i`,
-- for example `<Int, ♣>` - remember `ENDO i` only has one object (`♣`)
-- An arrow of `TYPE×ENDO i` is one arrow from `TYPE` and one from `ENDO i` such
-- that the objects are taken pair-wise as follows:
-- Given `f ∷ Int ▷ String` (from `TYPE`) and `g ∷ ♣ ▷ ♣` (from `ENDO i`)
-- We have the arrow `<f, g> ∷ <Int, ♣> ▷ <String, ♣>`
-- This could be modelled in Haskell with `(TYPExENDO i) Int String`:
-- We don't mention objects of `ENDO i` as type arguments
-- because there's only one thing they could be (`♣`).
data (TYPExENDO i) d c = TypeEndo (d → c) (ENDO i)
-- composition pairwise delegates to the underlying categories
-- ∘ = <∘, ∘> ∷ ∀ a b x . (<a, ♣> ▷ <b, ♣>) → (<x, ♣> ▷ <a, ♣>) → (<x, ♣> ▷ <b, ♣>)
compose_TYPExENDO ∷ ∀ i a b x .
  (TYPExENDO i) a b → (TYPExENDO i) x a → (TYPExENDO i) x b
compose_TYPExENDO (TypeEndo ab l) (TypeEndo xa r) =
  TypeEndo (compose_TYPE ab xa) (compose_ENDO l r)
-- as is identity:
-- id = <id, id> ∷ ∀ x . <x, ♣> ▷ <x, ♣>
id_TYPExENDO ∷ ∀ i x . (TYPExENDO i) x x
id_TYPExENDO = TypeEndo id_TYPE id_ENDO


-- For every category, there is an 'opposite' category.
-- This is exactly the same category, but we look at all the arrows as if they
-- are going in the other direction.
-- In the category `TYPE`, the arrow type `d ▷ c` is the function type `d → c`.
-- When considering the opposite of `TYPE`: the `Op TYPE` category;
-- the same function type `d → c` corresponds with the arrow type `c ▷ d`,
-- and the arrow type `d ▷ c` is the function type `c → d`.
-- (∘) ∷ ∀ a b x . (a ▷ b) → (x ▷ a) → (x ▷ b)
compose_OpTYPE ∷ ∀ a b x . (b → a) → (a → x) → (b → x)
compose_OpTYPE ba ax b = ax (ba b)
-- the identity arrows are identical
id_OpTYPE ∷ ∀ i . i → i
id_OpTYPE i = i


-- Suppose we take the cross product of `Op TYPE` and `TYPE`: `OpType×TYPE`.
-- Objects are pairs of objects, first from `Op TYPE` and second from `TYPE`:
-- e.g: `<a, b>`.
-- Arrows are pairs: `<f, g> ∷ <a, b> ▷ <s, t>`
-- An arrows types such as `<a, b> ▷ <s, t>` can be modelled in Haskell
-- as `OpTYPExTYPE a b s t`:
data OpTYPExTYPE a b s t = OpTypeType (s → a) (b → t)
compose_OpTYPExTYPE ∷ ∀ a b s t x y .
  OpTYPExTYPE a b s t → OpTYPExTYPE x y a b → OpTYPExTYPE x y s t
compose_OpTYPExTYPE (OpTypeType sa bt) (OpTypeType ax yb) =
  OpTypeType (compose_OpTYPE sa ax) (compose_TYPE bt yb)
-- id = <id, id> ∷ <x, y> ▷ <x, y>
id_OpTYPExTYPE ∷ ∀ x y . OpTYPExTYPE x y x y
id_OpTYPExTYPE = OpTypeType id_OpTYPE id_TYPE


-- Now that we've introduced some categories
-- lets take a look at functors

-- functors map from one category to another
-- a functor `F` from a category `C` to a category `D`
-- maps objects `A` of `C` to objects `F A` of `D`
-- maps arrows `q ∷ A ▷ B` in `C`
-- to an arrow `F q ∷ F A ▷ F B` in `D`
-- think of the `F q` bit in a similar way to `fmap q`


-- TODO

-- for any category `C` and any object `X`, it turns out that
-- the partially-applied arrow type `X ▷ _` is a functor from `C` to `TYPE`
-- it maps `C`-objects `B` to `TYPE`-objects `(X ▷ _) B`, which is the type `X ▷ B`
-- it maps `C`-arrows `f ∷ A ▷ B` to `TYPE`-arrows `(X ▷ _) f ∷ (X ▷ A) ▷ (X ▷ B)`
-- which is the function `(X ▷ _) f ∷ (X ▷ A) → (X ▷ B)`
-- this mapping on arrows is actually partially applied composition:
-- `(X ▷ _) ∷ (A ▷ B) → (X ▷ _) A → (X ▷ _) B`
-- `(X ▷ _) ∷ (A ▷ B) → (X ▷ A) → (X ▷ B)`
-- `(X ▷ _) ab xa = ab ∘ xa`

-- This `(X ▷ _)` is an example of what is called a (covariant) "Yoneda Embedding".
-- Another "Yoneda Embedding" would be `(_ ▷ Y)`, however this would be a
-- contravariant functor from `C`.  That is, it maps from `Op C`.
-- It maps `Op C`-objects `A` to `TYPE`-objects `(_ ▷ Y) A`,
-- which is the type `A ▷ Y`.
-- It maps `Op C`-arrows `f ∷ A ▷ B` to `TYPE`-arrows `(_ ▷ Y) f ∷ (B ▷ Y) ▷ (A ▷ Y)`
-- Again, this mapping on arrows is actually partially applied composition:
-- `(_ ▷ Y) ∷ (A ▷ B) → (_ ▷ Y) B → (_ ▷ Y) A`
-- `(_ ▷ Y) ∷ (A ▷ B) → (B ▷ Y) → (A ▷ Y)`
-- `(_ ▷ Y) ab by = by ∘ ab`

-- Let's pick some categories and look at what the "Yoneda Embedding"s look like.

-- Suppose we are looking at the category `ALL`.
-- We can model functors from `ALL` to `TYPE` by a type class such as:

-- functors `f` from `ALL` to `TYPE`
class ALLTo f where
  -- allMap ∷ ∀ a b . (a ▷ b) → (f a ▷ f b)
  -- allMap ∷ (♣ ▷ ♣) → (f ♣ ▷ f ♣)
  allMap ∷ ALL → f → f

-- This may look a bit odd, but because (like before) there is only one object
-- in `ALL` (`♣`), so we can trivially omit it.

-- The covariant Yoneda Embedding `(♣ ▷ _)` is such a functor
-- with the mapping function `(♣ ▷ _)` being `(∘)` in `ALL`,
-- (as described previously).

-- instance ALLTo (♣ ▷ _) where
instance ALLTo ALL where
  -- allMap ∷ (♣ ▷ ♣) → (♣ ▷ _) ♣ → (♣ ▷ _) ♣
  -- allMap ∷ (♣ ▷ ♣) → (♣ ▷ ♣) → (♣ ▷ ♣)
  allMap ∷ ALL → ALL → ALL
  allMap = compose_ALL

-- To look at the contravariant Yoneda Embedding from `ALL`, we'll want to
-- introduce contravariant functors from `ALL`.
-- That is, functors from `ALL` to `TYPE`
-- But because all the objects are trivial, this class will look identical to
-- the covariant version

class ContraALLTo f where
  -- contraAllMap ∷ ∀ a b . (a ▷ b) → (f a ▷ f b)
  --                        ^(Op ALL) ^TYPE
  --                        ^ALL      ^(Op TYPE)
  -- contraAllMap ∷ ∀ a b . (a ▷ b) → (f b ▷ f a)
  --                        ^ALL      ^TYPE
  --                        ^(Op All) ^(Op TYPE)
  -- contraAllMap ∷ (♣ ▷ ♣) → (f ♣ ▷ f ♣)
  contraAllMap ∷ ALL → f → f

-- In the above, I have annotated (`^`) which categories the arrow types could
-- be considered to be from.

-- Note: for (covariant) functors from `Op C` to `D`, we can equivalently
-- describe them as (covariant) functors from `C` to `Op D`, or as
-- contravariant functors from `C` to `D`.  These are all the same thing.
-- So in this type signature of `contraAllMap`:

-- TODO
newtype DualALL = DualAll ALL

-- TODO
instance ContraALLTo DualALL where
  contraAllMap f (DualAll g) = DualAll (compose_ALL g f)


-- TODO

-- functors `f` from `TYPE` to `TYPE`
class TYPETo f where
  -- typeMap ∷ ∀ a b . (a ▷ b) → (f a ▷ f b)
  typeMap ∷ ∀ a b . (a → b) → (f a → f b)

-- functors `f` from `TYPE` to `TYPE`
class ContraTYPETo f where
  -- contraTypeMap ∷ ∀ a b . (a ▷ b) → (f b ▷ f a)
  contraTypeMap ∷ ∀ a b . (a → b) → (f b → f a)




-- TODO

-- ALLYoneda f a = ∀ b . (a ▷ b) → f b
-- ALLYoneda f ♣ = (♣ ▷ ♣) → f ♣
newtype ALLYoneda f = AllYoneda (ALL → f)

instance ALLTo (ALLYoneda f) where
  allMap a (AllYoneda y) = AllYoneda (\b → y (compose_ALL a b))

-- toALLYoneda ∷ ∀ f a . ALLTo f a ⇒ f a → ALLYoneda f a
-- toALLYoneda ∷ ∀ f . ALLTo f ♣ ⇒ f ♣ → ALLYoneda f ♣
toALLYoneda ∷ ∀ f . ALLTo f ⇒ f → ALLYoneda f
toALLYoneda f = AllYoneda (\a → allMap a f)

-- unALLYoneda ∷ ∀ f a . ALLYoneda f a → f a
-- unALLYoneda ∷ ∀ f . ALLYoneda f ♣ → f ♣
unALLYoneda ∷ ∀ f . ALLYoneda f → f
unALLYoneda (AllYoneda y) = y id_ALL


-- type ALLCoyoneda f b = ∃ a . ( a ▷ b , f a )
-- type ALLCoyoneda f ♣ = ( ♣ ▷ ♣ , f ♣ )
data ALLCoyoneda f = AllCoyoneda ALL f

instance ALLTo (ALLCoyoneda f) where
  allMap a (AllCoyoneda b f) = AllCoyoneda (compose_ALL a b) f

toALLCoyoneda ∷ ∀ f . ALL → f → ALLCoyoneda f
toALLCoyoneda a f = AllCoyoneda a f

liftALLCoyoneda ∷ ∀ f . f → ALLCoyoneda f
liftALLCoyoneda f = AllCoyoneda id_ALL f

lowerALLCoyoneda ∷ ∀ f . ALLTo f ⇒ ALLCoyoneda f → f
lowerALLCoyoneda (AllCoyoneda a f) = allMap a f

-- ∀ f a . ALLTo f ⇒ ( f a ≅ ALLCoyoneda f a )
-- ∀ f ♣ . ALLTo f ⇒ ( f ♣ ≅ ALLCoyoneda f ♣ )
-- ∀ f . ALLTo f ⇒ ( f ≅ ALLCoyoneda f )


-- ALLYonedaO a b = ∀ f . ALLTo f ⇒ f a → f b
-- ALLYonedaO ♣ ♣ = ∀ f . ALLTo f ⇒ f ♣ → f ♣
type ALLYonedaO = ∀ f . ALLTo f ⇒ f → f

-- toALLYonedaO ∷ ∀ a b . (a ▷ b) → ALLYonedaO a b
-- toALLYonedaO ∷ (♣ ▷ ♣) → ALLYonedaO ♣ ♣
toALLYonedaO ∷ ALL → ALLYonedaO
toALLYonedaO = allMap

-- toALLYonedaO ∷ ∀ a b . ALLYonedaO a b → (a ▷ b)
-- toALLYonedaO ∷ ALLYonedaO ♣ ♣ → (♣ ▷ ♣)
unALLYonedaO ∷ ALLYonedaO → ALL
unALLYonedaO y = y id_ALL

-- ∀ a b . ( (a ▷ b) ≅ ALLYonedaO a b )
-- (♣ ▷ ♣) ≅ ALLYonedaO ♣ ♣
-- ALL ≅ ALLYonedaO



-- TYPEYoneda f a = ∀ b . (a ▷ b) → f b
newtype TYPEYoneda f a = TypeYoneda (∀ b . (a → b) → f b)

instance TYPETo (TYPEYoneda f) where
  typeMap ∷ ∀ a b . (a → b) → (TYPEYoneda f a → TYPEYoneda f b)
  typeMap a2b (TypeYoneda y) = TypeYoneda (\b2c → y (compose_TYPE b2c a2b))

-- TYPECoyoneda f b = ∃ a . ( a ▷ b, f a )
-- TYPECoyoneda f b = ∃ a . ( a → b, f a )
data TYPECoyoneda f b = ∀ a . TypeCoyoneda (a → b) (f a)

-- TYPEYonedaO a b = ∀ g . TYPETo g ⇒ (g a ▷ g b)


