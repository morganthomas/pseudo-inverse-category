{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}


{-|
   A pseudo-inverse category is a category where every morphism has a pseudo-inverse.
-}


module Control.PseudoInverseCategory (
  -- * Classes
  ToHask (..)
  , HasHaskFunctors (..)
  , PseudoInverseCategory (..)
  , PIArrow (..)
  , piswap
  , piassoc
  -- * EndoIso
  , EndoIso (..)
  , pimap
  ) where


import qualified Control.Categorical.Functor as F
import           Control.Category            (Category (..))
import           Data.Bifunctor              (bimap, first, second)
import           Data.Functor.Identity       (Identity (..))
import           Data.Tuple                  (swap)
import           Shpadoinkle.Continuation    (Continuation (..), contIso, mapC)
import           Shpadoinkle.Core            (Html (..), Prop (..), Props (..))
import           Prelude                     hiding (id, (.))


-- | A type satisfying this class is a functor from another category to Hask. Laws:
--
-- prop> piapply (f . g) = piapply f . piapply g
-- prop> piapply id = id
--
class Category a => ToHask a where
  piapply :: a x y -> x -> y


-- | For any type @a@ satisfying this class, we can lift endofunctors of Hask into @a@.
--   This mapping should constitute a functor from one monoidal category of endofunctors
--   to the other. That statement defines the applicable laws, which are, in other words:
--
--   prop> fmapA id = id
--   prop> fmapA (f >>> g) = fmapA f >>> fmapA g
class Category a => HasHaskFunctors a where
  fmapA :: Functor f => a x y -> a (f x) (f y)


-- | A pseudo-inverse category is a category where every morphism has a pseudo-inverse.
--  What this means is defined by the following laws (perhaps things can be removed
--  and perhaps things should be added):
--
-- prop> pipower 1 f = f
-- prop> pileft (pipower 0 f) = id
-- prop> piright (pipower 0 f) = id
-- prop> pipower (n+1) f = pileft f . pipower n f
-- prop> piinverse (piinverse f) = f
-- prop> f . piinverse f = piright (pipower 2 f)
-- prop> piinverse f . f = pileft (pipower 2 f)
-- prop> pileft (piright f) = piright (piright f) = piright f
-- prop> piright (pileft f) = pileft (pileft f) = pileft f
-- prop> piinverse (pileft f) = pileft f
-- prop> piinverse (piright f) = piright f
--
class Category a => PseudoInverseCategory a where
  -- | Apply a morphism /n/ times, /n/ >= 0.
  pipower :: Int -> a x y -> a x y

  -- | Change a morphism into an endomorphism of its domain.
  pileft :: a x y -> a x x

  -- | Change a morphism into an endomorphism of its codomain.
  piright :: a x y -> a y y

  -- | Pseudo-invert a morphism. The pseudo-inverse of a morphism may or may not
  --   be its inverse. @f@ is the inverse of @g@ means that @f.g = id@ and @g.f = id@.
  --   If @f@ has an inverse, then @piinverse f@ may or may not be the inverse
  --   of @f@.
  piinverse :: a x y -> a y x


-- | An analogue of the Arrow typeclass for pseudo-inverse categories. Laws:
--
-- prop> piiso id id = id
-- prop> piendo id = id
-- prop> piiso (f . g) (h . i) = piiso f h . piiso g i
-- prop> piendo (f . h) = piendo f . piendo h
-- prop> pifirst (piiso f g) = piiso (first f) (first g)
-- prop> pifirst (piendo f) = piendo (first f)
-- prop> pifirst (f . g) = pifirst f . pifirst g
-- prop> pisplit id g . pifirst f = pifirst f . pisplit id g
-- prop> piassoc . first (first f) = first f . piassoc
-- prop> pisecond f = piswap . pifirst f . piswap
-- prop> pisplit f g = pifirst f . pisecond g
-- prop> pifan f g = piiso (\b -> (b,b)) fst . pisplit f g
-- prop> piinverse (piiso f g) = piiso g f
-- prop> piinverse (piendo f) = piendo f
-- prop> piapply (piiso f g) = f
-- prop> piapply (piinverse (piiso f g)) = g
-- prop> piapply (piendo f) = f
--
class PseudoInverseCategory a => PIArrow a where
  -- | Create an arrow from an isomorphism (restricted version of arr).
  piiso :: (b -> c) -> (c -> b) -> a b c

  -- | Create an arrow from an endomorphism (restricted version of arr).
  piendo :: (b -> b) -> a b b

  -- | Apply an arrow to the first coordinate of a tuple.
  pifirst :: a b c -> a (b, d) (c, d)

  -- | Apply an arrow to the second coordinate of a tuple.
  pisecond :: a b c -> a (d, b) (d, c)

  -- | Combine two arrows to work in parallel on a tuple.
  pisplit :: a b c -> a d e -> a (b, d) (c, e)

  -- | Combine two arrows on the same input to output a tuple.
  pifan :: a b c -> a b d -> a b (c, d)


-- | Every pseudo-inverse category has isomorphisms to swap the coordinates of a tuple.
piswap :: PIArrow a => a (b, c) (c, b)
piswap = piiso swap swap


-- | Every pseudo-inverse category has isomorphisms to change the associativity of a 3-tuple.
piassoc :: PIArrow a => a ((b,c),d) (b,(c,d))
piassoc = piiso (\((x,y),z) -> (x,(y,z))) (\(x,(y,z)) -> ((x,y),z))


-- | This is a pseudo-inverse category where a morphism is a composition of an endomorphism
--   on the domain and an isomorphism of the domain with the codomain.
--   The last two arguments are required to form an isomorphism, i.e. for all @EndoIso f g h@:
--
-- prop> g . h = id
-- prop> h . g = id
--
-- This category contains as objects all types in Hask and as morphisms all compositions
-- of endomorphisms and isomorphisms in Hask.
data EndoIso a b = EndoIso (a -> a) (a -> b) (b -> a)


instance Category EndoIso where
  id = EndoIso id id id

  EndoIso i j k . EndoIso f g h = EndoIso (f . h . i . g) (j . g) (h . k)


instance F.Functor EndoIso (->) Identity where
  map (EndoIso f g _) = Identity . g . f . runIdentity


instance ToHask EndoIso where
  piapply (EndoIso f g _) = g.f


pimap :: F.Functor EndoIso EndoIso f => EndoIso a b -> f a -> f b
pimap = (\(EndoIso f g _) -> g.f) . F.map


instance HasHaskFunctors EndoIso where
  fmapA (EndoIso f g h) = EndoIso (fmap f) (fmap g) (fmap h)


instance PseudoInverseCategory EndoIso where
  pipower n (EndoIso f g h)
    | n < 0 = error "pipower with n < 0"
    | n > 0 = let EndoIso f' _ _ = pipower (n-1) (EndoIso f g h) in EndoIso (f.f') g h
    | otherwise = EndoIso id g h
  pileft (EndoIso f _ _) = EndoIso f id id
  piright (EndoIso f g h) = EndoIso (g.f.h) id id
  piinverse (EndoIso f g h) = EndoIso (g.f.h) h g


instance PIArrow EndoIso where
  piiso = EndoIso id
  piendo f = EndoIso f id id
  pifirst (EndoIso f g h) = EndoIso (first f) (first g) (first h)
  pisecond (EndoIso f g h) = EndoIso (second f) (second g) (second h)
  pisplit (EndoIso f g h) (EndoIso i j k) = EndoIso
    (bimap f i)
    (bimap g j)
    (bimap h k)
  pifan (EndoIso f g h) (EndoIso i j _) = EndoIso
    (f . i)
    (\x -> (g x, j x))
    (\(x,_) -> h x) -- it shouldn't matter which side we use to go back because we have isomorphisms


-- | @Continuation m@ is a Functor in the EndoIso category (where the objects
--   are types and the morphisms are EndoIsos).
instance Applicative m => F.Functor EndoIso EndoIso (Continuation m) where
  map :: EndoIso a b -> EndoIso  (Continuation m a) (Continuation m b)
  map (EndoIso f g h) =
    EndoIso (Continuation f . const . pure) (contIso g h) (contIso h g)


-- | @Html m@ is a functor in the EndoIso category, where the objects are
--   types and the morphisms are EndoIsos.
instance Applicative m => F.Functor EndoIso EndoIso (Html m) where
  map (EndoIso f g i) = EndoIso (mapC . piapply $ map' (piendo f))
                                (mapC . piapply $ map' (piiso g i))
                                (mapC . piapply $ map' (piiso i g))
    where map' :: EndoIso a b -> EndoIso (Continuation m a) (Continuation m b)
          map' = F.map
  {-# INLINE map #-}


-- | Prop is a functor in the EndoIso category, where the objects are types
--  and the morphisms are EndoIsos.
instance Applicative m => F.Functor EndoIso EndoIso (Prop m) where
  map :: forall a b. EndoIso a b -> EndoIso (Prop m a) (Prop m b)
  map f = EndoIso id mapFwd mapBack
    where f' :: EndoIso (Continuation m a) (Continuation m b)
          f' = F.map f

          mapFwd :: Prop m a -> Prop m b
          mapFwd (PData t)     = PData t
          mapFwd (PText t)     = PText t
          mapFwd (PFlag t)     = PFlag t
          mapFwd (PListener g) = PListener $ \r e -> piapply f' <$> g r e
          mapFwd (PPotato p)   = PPotato $ fmap (fmap (piapply f')) . p


          mapBack :: Prop m b -> Prop m a
          mapBack (PData t)     = PData t
          mapBack (PText t)     = PText t
          mapBack (PFlag t)     = PFlag t
          mapBack (PListener g) = PListener $ \r e -> piapply (piinverse f') <$> g r e
          mapBack (PPotato b)   = PPotato $ fmap (fmap (piapply (piinverse f'))) . b
  {-# INLINE map #-}


-- | Props is a functor in the EndoIso category, where the objects are
--  types and the morphisms are EndoIsos.
instance Applicative m => F.Functor EndoIso EndoIso (Props m) where
  map f = piiso Props getProps . fmapA (F.map f) . piiso getProps Props
  {-# INLINE map #-}
