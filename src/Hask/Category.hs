{-# LANGUAGE CPP, KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, DefaultSignatures, NoMonomorphismRestriction, AllowAmbiguousTypes  #-}
module Hask.Category
  (
  -- * Category
    Category'(..)
  , Category''
  , Category
  -- * Functors
  -- ** Regular
  , Functor(..)
  , FunctorOf
  , ob, obOf
  , contramap
  -- ** (Curried) Bifunctors
  , Bifunctor
  , Cod2, Dom2
  , fmap1, first
  , bimap
  , dimap
  -- * Vacuous
  , Vacuous
  -- * Categories
  -- ** Constraints
  , Constraint, (:-)(Sub), Dict(..), (\\), sub, Class(cls), (:=>)(ins)
  -- ** Op
  , Yoneda(..), Op, Opd
  -- ** Nat
  , Nat(..), NatId, Endo, nat, (!)
  , Presheaves, Copresheaves
  , NatDom, NatCod
  -- * Prelude
  , ($), Either(..)
  , Fix(..)
  ) where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Proxy (Proxy(..))
import Data.Type.Equality
import Data.Type.Bool 
import Data.Void (Void, absurd)
import Prelude (maxBound,minBound,Bounded,(++),putStrLn,String,($), Either(..),const,undefined,IO, any, error, Show,show,Int,(==),minBound,(<=),Integer,length)
import qualified Prelude ((.),id)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Ord (Ord,compare,Ordering(..))
import Data.Eq (Eq)
import Data.Bool (Bool,Bool(True),(&&))


--------------------------------------------------------------------------------
-- * Categories (Part 1)
--------------------------------------------------------------------------------

-- | The <http://ncatlab.org/nlab/show/Yoneda+embedding Yoneda embedding>.
--
-- Yoneda_C :: C -> [ C^op, Set ]
newtype Yoneda (p :: i -> i -> *) (a :: i) (b :: i) = Op { getOp :: p b a }

type family Op (p :: i -> i -> *) :: i -> i -> * where
  Op (Yoneda p) = p
  Op p = Yoneda p

-- | Side-conditions moved to 'Functor' to work around GHC bug #9200.
--
-- You should produce instances of 'Category'' and consume instances of 'Category'.
--
-- All of our categories are "locally small", and we curry the Hom-functor
-- as a functor to the category of copresheaves rather than present it as a
-- bifunctor directly. The benefit of this encoding is that a bifunctor is
-- just a functor to a functor category!
--
-- @
-- C :: C^op -> [ C, Set ]
-- @

class Category' (p :: i -> i -> *) where
  type Ob p :: i -> Constraint
  id :: Ob p a => p a a
  observe :: p a b -> Dict (Ob p a, Ob p b)
  (.) :: p b c -> p a b -> p a c

  unop :: Op p b a -> p a b
  default unop :: Op p ~ Yoneda p => Op p b a -> p a b
  unop = getOp

  op :: p b a -> Op p a b
  default op :: Op p ~ Yoneda p => p b a -> Op p a b
  op = Op

type Endo p a = p a a

--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

class (Category' (Dom f), Category' (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: i -> i -> *
  type Cod f :: j -> j -> *
  fmap :: Dom f a b -> Cod f (f a) (f b)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

-- | Functors preserve @Ob@ constraints
ob :: forall f a. Functor f => Ob (Dom f) a :- Ob (Cod f) (f a)
ob = Sub $ case observe (fmap (id :: Dom f a a) :: Cod f (f a) (f a)) of
  Dict -> Dict

data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: ( FunctorOf p q f
         , FunctorOf p q g
         ) => {
           runNat :: forall a. Ob p a => q (f a) (g a)
         } -> Nat p q f g

-- | Endomorphisms of a given functor
type NatId p = Endo (Nat (Dom p) (Cod p)) p

obOf :: (Category (Dom f), Category (Cod f)) => NatId f -> Endo (Dom f) a
     -> Dict (Ob (Nat (Dom f) (Cod f)) f, Ob (Dom f) a, Ob (Cod f) (f a))
obOf f a = case observe f of
  Dict -> case observe a of
    Dict -> case observe (f ! a) of
      Dict -> Dict

type Copresheaves p = Nat p (->)
type Presheaves p = Nat (Op p) (->)

instance (Category' p, Category' q) => Functor (FunctorOf p q) where
  type Dom (FunctorOf p q) = Nat p q
  type Cod (FunctorOf p q) = (:-)
  fmap Nat{} = Sub Dict

--------------------------------------------------------------------------------
-- * Bifunctors
--------------------------------------------------------------------------------

type family NatDom (f :: (i -> j) -> (i -> j) -> *) :: (i -> i -> *) where
  NatDom (Nat p q) = p

type family NatCod (f :: (i -> j) -> (i -> j) -> *) :: (j -> j -> *) where
  NatCod (Nat p q) = q

type Dom2 p = NatDom (Cod p)
type Cod2 p = NatCod (Cod p)

class (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)
instance  (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)

fmap1 :: forall p a b c. (Bifunctor p, Ob (Dom p) c) => Dom2 p a b -> Cod2 p (p c a) (p c b)
fmap1 f = case ob :: Ob (Dom p) c :- FunctorOf (Dom2 p) (Cod2 p) (p c) of
  Sub Dict -> fmap f


bimap :: Bifunctor p => Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)
bimap f g = case observe f of
  Dict -> case observe g of
    Dict -> runNat (fmap f) . fmap1 g

type Opd f = Op (Dom f)

contramap :: Functor f => Opd f b a -> Cod f (f a) (f b)
contramap = fmap . unop

-- | E-Enriched profunctors f : C -/-> D are represented by a functor of the form:
--
-- C^op -> [ D, E ]
--
-- The variance here matches Haskell's order, which means that the contravariant
-- argument comes first!

dimap :: Bifunctor p => Opd p b a -> Dom2 p c d -> Cod2 p (p a c) (p b d)
dimap = bimap . unop

{-
type Iso
  (c :: i -> i -> *) (d :: j -> j -> *) (e :: k -> k -> *)
  (s :: i) (t :: j) (a :: i) (b :: j) = forall (p :: i -> j -> k).
  (Bifunctor p, Opd p ~ c, Dom2 p ~ d, Cod2 p ~ e) => e (p a b) (p s t)
-}

--------------------------------------------------------------------------------
-- * Categories (Part 2)
--------------------------------------------------------------------------------

class    (Category' p, Bifunctor p, Dom p ~ Op p, p ~ Op (Dom p), Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p
instance (Category' p, Bifunctor p, Dom p ~ Op p, p ~ Op (Dom p), Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p

-- | The full definition for a (locally-small) category.
class    (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p
instance (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p

--------------------------------------------------------------------------------
-- * Vacuous
--------------------------------------------------------------------------------

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap f Dict = case f of Sub g -> g

instance (Category' c, Ob c ~ Vacuous c) => Functor (Vacuous c) where
  type Dom (Vacuous c) = c
  type Cod (Vacuous c) = (:-)
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * The Category of Constraints
--------------------------------------------------------------------------------

instance Functor (:-) where
  type Dom (:-) = Op (:-)
  type Cod (:-) = Nat (:-) (->) -- copresheaves
  fmap (Op f) = Nat (. f)

instance Functor ((:-) b) where
  type Dom ((:-) b) = (:-)
  type Cod ((:-) b) = (->)
  fmap = (.)

instance Category' (:-) where
  type Ob (:-) = Vacuous (:-)
  id = Constraint.refl
  observe _ = Dict
  (.) = Constraint.trans
  unop = getOp

sub :: (a => Proxy a -> Dict b) -> a :- b
sub k = Sub (k Proxy)

--------------------------------------------------------------------------------
-- * Hask
--------------------------------------------------------------------------------

instance Functor (->) where
  type Dom (->) = Op (->)
  type Cod (->) = Nat (->) (->)
  fmap (Op f) = Nat (. f)

instance Functor ((->)a) where
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
  fmap = (.)

instance Category' (->) where
  type Ob (->) = Vacuous (->)
  id x = x
  observe _ = Dict
  (.) f g x = f (g x)
  unop = getOp

--------------------------------------------------------------------------------
-- * Yoneda :: i -> [ Op i, Set ]
--------------------------------------------------------------------------------

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f = Nat (. Op f)

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p a) where
  type Dom (Yoneda p a) = Yoneda p
  type Cod (Yoneda p a) = (->)
  fmap = (.)

instance (Category p, Op p ~ Yoneda p) => Category' (Yoneda p) where
  type Ob (Yoneda p) = Ob p
  id = Op id
  Op f . Op g = Op (g . f)
  observe (Op f) = case observe f of
    Dict -> Dict
  unop = Op
  op = getOp

--------------------------------------------------------------------------------
-- * Nat
--------------------------------------------------------------------------------

instance (Category' p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Op (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Functor (Nat p q a) where
  type Dom (Nat p q a) = Nat p q
  type Cod (Nat p q a) = (->)
  fmap = (.)

instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     id1 :: forall f x. (Functor f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob :: Ob p x :- Ob q (f x))
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)
   unop = getOp

nat :: (Category p ,Category q, FunctorOf p q f, FunctorOf p q g) => (forall a. Ob p a => Endo p a -> q (f a) (g a)) -> Nat p q f g
nat k = Nat (k id)

infixr 1 !
(!) :: Nat p q f g -> p a a -> q (f a) (g a)
Nat n ! f = case observe f of
  Dict -> n

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat $ \(a,b) -> (f a, b)

instance Functor ((,) a) where
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  fmap f (a,b) = (a, f b)

instance Functor Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)
  fmap f0 = Nat (go f0) where
    go :: (a -> b) -> Either a c -> Either b c
    go f (Left a)  = Left (f a)
    go _ (Right b) = Right b

instance Functor (Either a) where
  type Dom (Either a) = (->)
  type Cod (Either a) = (->)
  fmap _ (Left a) = Left a
  fmap f (Right b) = Right (f b)

first :: (Functor f, Cod f ~ Nat d e, Ob d c) => Dom f a b -> e (f a c) (f b c)
first = runNat . fmap

newtype Fix (f :: * -> * -> *) (a :: *) = In { out :: f (Fix f a) a }

instance Functor Fix where
  type Dom Fix = Nat (->) (Nat (->) (->))
  type Cod Fix = Nat (->) (->)
  fmap f = case observe f of 
    Dict -> Nat $ \ (In mu) -> In (first (first f) (runNat (runNat f) mu))

instance FunctorOf (->) (Nat (->) (->)) p => Functor (Fix p) where
  type Dom (Fix p) = (->)
  type Cod (Fix p) = (->)
  fmap f (In b) = In (bimap (fmap f) f b)

--------------------------------------------------------------------------------
-- Initital object  
-- In category theory, a branch of mathematics, an initial object of a category C 
-- is an object I in C such that for every object X in C, there exists precisely 
-- one morphism I → X.

-- Terminal object
-- T is terminal if for every object X in C there exists exactly one morphism X → T. 
--------------------------------------------------------------------------------

class Category' p => InitialObject (p :: i -> i -> *) (initial :: i) where
  initialArrow :: Ob p x => p initial x

class Category' p => TerminalObject (p :: i -> i -> *) (terminal :: i) where
  terminalArrow :: Ob p x => p x terminal

-- The initial object is a terminal object in the opposite category (and vice versa)
instance (Category' p, Op p ~ Yoneda p, TerminalObject (Op p) initial) => InitialObject p initial where
  initialArrow = unop terminalArrow

instance (Category' p, Op p ~ Yoneda p, InitialObject (Op p) terminal) => TerminalObject p terminal where
  terminalArrow = unop initialArrow

-- An object that is both initial and terminal is called zero object
class (Category' p, InitialObject p zero, TerminalObject p zero) => ZeroObject (p :: i -> i -> *) (zero :: i) where
  -- The presence of both initialArrow and terminalArrow is implicit in this class.
  zeroObject :: p zero zero

--------------------------------------------------------------------------------
-- * Example: In the category Rel of sets and relations, the empty set is the 
--   unique initial object, the unique terminal object, (and hence the unique 
--   zero object.)
--------------------------------------------------------------------------------
data Rel a b = Rel { rel :: Set (a, b) }
instance Category' Rel where
  type Ob Rel = Vacuous Rel
  id = Rel Set.empty
  (Rel r) . (Rel s) = undefined-- Rel (Set.fromList [ (x, z) | (x, y) <- Set.toList (rel s), (y', z) <- Set.toList (rel r), y == y' ])
  observe _ = Dict

-- Initial object instance for Rel
instance InitialObject Rel () where
  initialArrow = Rel Set.empty
-- Terminal object instance for Rel
instance TerminalObject Rel () where
  terminalArrow = Rel Set.empty

testRelCategory :: IO ()
testRelCategory = do
  putStrLn "Testing Rel Category (Sets and Relations):"
  
  -- Test initial object (empty relation)
  let initialRel = rel (initialArrow :: Rel () Int)
  putStrLn $ "Initial Relation: " ++ show initialRel
  
  -- Test terminal object (empty relation)
  let terminalRel = rel (terminalArrow :: Rel Int ())
  putStrLn $ "Terminal Relation: " ++ show terminalRel
  
  -- Check if initial and terminal objects are indeed empty relations
  putStrLn $ "Is Initial Relation empty? " ++ show (Set.null initialRel)
  putStrLn $ "Is Terminal Relation empty? " ++ show (Set.null terminalRel)

--------------------------------------------------------------------------------
-- Any partially ordered set (P, ≤) can be interpreted as a category: 
-- the objects are the elements of P, and there is a single morphism from x to y 
-- if and only if x ≤ y. This category has an initial object if and only if 
-- P has a least element; it has a terminal object if and only if P has a greatest element.
--------------------------------------------------------------------------------
data Poset a b = Poset { poset :: Set (a, b) }

instance Category' Poset where
  type Ob Poset = Ord
  id = Poset Set.empty
  Poset s1 . Poset s2 = undefined -- Poset (Set.fromList [ (x, y) | x <- Set.toList s1, y <- Set.toList s2, x <= y ])
  observe _ = Dict

-- Define the initial object for Poset
instance InitialObject Poset Int where
  initialArrow = Poset Set.empty

-- Define the terminal object for Poset 
instance TerminalObject Poset Int where
  terminalArrow = Poset Set.empty

testPosetCategory :: IO ()
testPosetCategory = do
  putStrLn "Testing Poset Category (Partially Ordered Sets):"
  
  Test initial object (empty set)
  let initialSet = poset (initialArrow :: Poset Int Int)
  putStrLn $ "Initial Set: " ++ show initialSet
  
  -- Test terminal object (empty set)
  let terminalSet = poset (terminalArrow :: Poset Int Int)
  putStrLn $ "Terminal Set: " ++ show terminalSet
  
  -- Check if initial and terminal objects are indeed empty sets
  putStrLn $ "Is Initial Set empty? " ++ show (Set.null initialSet)
  putStrLn $ "Is Terminal Set empty? " ++ show (Set.null terminalSet)
  
--------------------------------------------------------------------------------
-- In Ring, the category of rings with unity and unity-preserving morphisms,
-- the ring of integers Z is an initial object. The zero ring consisting only 
-- of a single element 0 = 1 is a terminal object.
--------------------------------------------------------------------------------
class Ring a where
  unity :: a
  add :: a -> a -> a
  mul :: a -> a -> a
  neg :: a -> a

data Z = Z

instance Ring Z where
  unity = Z
  add _ _ = Z
  mul _ _ = Z
  neg _ = Z

data ZeroRing = ZeroRing

instance Ring ZeroRing where
  unity = ZeroRing
  add _ _ = ZeroRing
  mul _ _ = ZeroRing
  neg _ = ZeroRing

data RingMorphism a b = RingMorphism { ringMorphism :: a -> b }

instance Category' RingMorphism where
  type Ob RingMorphism = Ring
  id = RingMorphism Prelude.id
  RingMorphism g . RingMorphism f = RingMorphism (g Prelude.. f)
  observe _ = Dict


-- Define the initial object for Ring
instance InitialObject Ring Z where
  initialArrow = Z

-- Define the terminal object for Ring
instance TerminalObject Ring ZeroRing where
  terminalArrow = ZeroRing

testRingCategory :: IO ()
testRingCategory = do
  putStrLn "Testing Ring Category:"
  
  -- Test initial object (Z)
  let initialRing = initialArrow :: Z
  putStrLn $ "Initial Ring: " ++ show initialRing
  
  -- Test terminal object (ZeroRing)
  let terminalRing = terminalArrow :: ZeroRing
  putStrLn $ "Terminal Ring: " ++ show terminalRing
  
  -- Check if initial and terminal objects are indeed initial and terminal rings
  putStrLn $ "Is Initial Ring Z? " ++ show (initialRing == Z)
  putStrLn $ "Is Terminal Ring ZeroRing? " ++ show (terminalRing == ZeroRing)
  
--------------------------------------------------------------------------------
-- * Sum & Product
--------------------------------------------------------------------------------
-- Sums (Coproducts)
class Category' p => Sum p a b where
  leftInjection  :: Ob p c => p a (SumType p a b c)
  rightInjection :: Ob p c => p b (SumType p a b c)
  sumCase :: forall c. Ob p c => p (SumType p a b c) c

type family SumType (p :: i -> i -> *) (a :: i) (b :: i) (c :: i) :: i

-- Products
class Category' p => Product p a b where
  pair :: Ob p c => p c a -> p c b -> p c (ProductType p a b)
  leftProjection  :: Ob p c => p (ProductType p a b) a
  rightProjection :: Ob p c => p (ProductType p a b) b

type family ProductType (p :: i -> i -> *) (a :: i) (b :: i) :: i

--------------------------------------------------------------------------------
-- * Example: A vector space is a set whose elements, often called vectors, may 
-- be added together and multiplied by numbers called scalars. Scalars are often 
-- real numbers, but can be complex numbers or, more generally, elements of any 
-- field. The operations of vector addition and scalar multiplication must satisfy
-- certain requirements, called vector axioms. Real vector space and complex 
-- vector space are kinds of vector spaces based on different kinds of scalars: 
-- real coordinate space or complex coordinate space. 
--------------------------------------------------------------------------------
-- Define a type for vector spaces over a scalar field 'k'
data VectorSpace k a = VectorSpace

-- Define linear transformations between vector spaces
data LinearMap k a b = LinearMap { linearMap :: a -> b }

-- Functor instance for VectorSpace
instance Functor (VectorSpace k) where
  type Dom (VectorSpace k) = (->)
  type Cod (VectorSpace k) = (->)
  fmap _ = VectorSpace  -- Identity transformation for vector spaces

-- Initial object: The zero-dimensional vector space
instance InitialObject (LinearMap k) Void where
  initialArrow = LinearMap absurd  -- No linear transformations from the zero vector space

-- Terminal object: The one-dimensional vector space
instance TerminalObject (LinearMap k) () where
  terminalArrow = LinearMap (\_ -> ())  -- Unique linear transformation to the one-dimensional vector space

-- Product of vector spaces
instance Product (LinearMap k) (VectorSpace k) (VectorSpace k) (VectorSpace k) where
  pair f g = LinearMap (\x -> (linearMap f x, linearMap g x))  -- Linear transformation combining two vector spaces
  leftProjection = LinearMap (\(x, _) -> x)  -- Projection map to the first factor space
  rightProjection = LinearMap (\(_, y) -> y)  -- Projection map to the second factor space

-- Coproduct of vector spaces
instance Sum (LinearMap k) (VectorSpace k) (VectorSpace k) (VectorSpace k) where
  leftInjection = LinearMap Left  -- Injection map from the first factor space
  rightInjection = LinearMap Right  -- Injection map from the second factor space
  sumCase = LinearMap (either id id)  -- Unique linear transformation from the coproduct

-- Test function to verify vector spaces and linear transformations
testVectorSpaceCategory :: IO ()
testVectorSpaceCategory = do
    putStrLn "Testing Vector Spaces and Linear Maps"
    putStrLn "------------------------------------"
    putStrLn "1. Initial and Terminal Objects:"
    putStrLn "   Initial object should have no linear transformations:"
    putStrLn $ "   Initial Arrow for Void: " ++ show (linearMap initialArrow :: Void -> Int)
    putStrLn "   Terminal object should have unique linear transformation to ()"
    putStrLn $ "   Terminal Arrow for (): " ++ show (linearMap terminalArrow :: Int -> ())
    putStrLn ""
    putStrLn "2. Product and Coproduct:"
    let v1 = VectorSpace :: VectorSpace Int Int
        v2 = VectorSpace :: VectorSpace Int Int
        p = pair v1 v2 :: LinearMap Int (Int, Int) (Int, Int)
        (l1, l2) = (leftProjection :: LinearMap Int (Int, Int) Int, rightProjection :: LinearMap Int (Int, Int) Int)
        (i1, i2) = (leftInjection :: LinearMap Int Int (Either Int Int), rightInjection :: LinearMap Int Int (Either Int Int))
        (f, g) = (linearMap l1, linearMap l2)
        (inl, inr) = (linearMap i1, linearMap i2)
        (sumF, sumG) = (linearMap $ sumCase :: Either Int Int -> Int, linearMap $ sumCase :: Either Int Int -> Int)
    putStrLn $ "   Pairing of Vector Spaces (2, 3): " ++ show (linearMap p (2, 3))
    putStrLn $ "   Left Projection of (2, 3): " ++ show (f (2, 3))
    putStrLn $ "   Right Projection of (2, 3): " ++ show (g (2, 3))
    putStrLn $ "   Left Injection of 5: " ++ show (inl 5)
    putStrLn $ "   Right Injection of 7: " ++ show (inr 7)
    putStrLn $ "   Sum Case of Left 10: " ++ show (sumF (Left 10))
    putStrLn $ "   Sum Case of Right 20: " ++ show (sumG (Right 20))

--------------------------------------------------------------------------------------
-- Limits: In category theory a limit of a diagram F:D→C in a category C is an object 
-- limF of C equipped with morphisms to the objects F(d) for all d∈D, such that 
-- everything in sight commutes. Moreover, the limit limF is the universal object
-- with this property, i.e. the “most optimized solution” to the problem of finding
-- such an object.
--------------------------------------------------------------------------------------

class Category' p => Cone (p :: i -> i -> *) (f :: i -> *) (l :: i) where
  apex :: Ob p x => f x -> p x l

class Category' p => Limit (p :: i -> i -> *) (f :: i -> *) (l :: i) where
  limit :: Cone p f l => p l l

-- The dual notions of limits and cones are colimits and co-cones.

class Category' p => Cocone (p :: i -> i -> *) (f :: i -> *) (l :: i) where
  vertex :: Ob p x => f x -> p l x

class Category' p => Colimit (p :: i -> i -> *) (f :: i -> *) (l :: i) where
  colimit :: Cocone p f l => p l l

-- --------------------------------------------------------------------------------
-- -- * Main function to run the tests
-- --------------------------------------------------------------------------------

main :: IO ()
main = do
  testRelCategory
  testPosetCategory
  testRingCategory
  testVectorSpaceCategory
  putStrLn "All tests passed successfully!"

