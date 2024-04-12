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
import qualified GHC.TypeLits as T


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

-- | The 'Category'' class represents a category in category theory.
-- It defines the basic operations and constraints for a category.
class Category' (p :: i -> i -> *) where
  -- | The 'Ob' type family specifies the constraint on objects in the category.
  type Ob p :: i -> Constraint
  -- | The 'id' function returns the identity morphism for a given object.
  id :: Ob p a => p a a
  -- | The 'observe' function takes a morphism and returns a dictionary of constraints
  -- on the source and target objects of the morphism.
  observe :: p a b -> Dict (Ob p a, Ob p b) 
  -- | The composition operator ('.') combines two morphisms to produce a new morphism.
  (.) :: p b c -> p a b -> p a c

  -- | The 'unop' function converts an opposite morphism to its corresponding morphism.
  unop :: Op p b a -> p a b
  default unop :: Op p ~ Yoneda p => Op p b a -> p a b
  unop = getOp

  -- | The 'op' function converts a morphism to its corresponding opposite morphism.
  op :: p b a -> Op p a b
  default op :: Op p ~ Yoneda p => p b a -> Op p a b
  op = Op

-- | The 'Endo' type synonym represents an endomorphism, which is a morphism from an object to itself.
type Endo p a = p a a

--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

-- | The 'Functor' class represents functors between categories.
class (Category' (Dom f), Category' (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: i -> i -> *
  type Cod f :: j -> j -> *
  fmap :: Dom f a b -> Cod f (f a) (f b)

-- | The 'FunctorOf' class represents functors between categories with specific domain and codomain categories.
class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

-- | Functors preserve @Ob@ constraints
ob :: forall f a. Functor f => Ob (Dom f) a :- Ob (Cod f) (f a)
ob = Sub $ case observe (fmap (id :: Dom f a a) :: Cod f (f a) (f a)) of
  Dict -> Dict

-- | The 'Nat' data type represents natural transformations between functors.
data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: ( FunctorOf p q f
         , FunctorOf p q g
         ) => {
           runNat :: forall a. Ob p a => q (f a) (g a)
         } -> Nat p q f g

-- | Endomorphisms of a given functor
type NatId p = Endo (Nat (Dom p) (Cod p)) p

-- | The 'obOf' function checks if the given natural transformation and object satisfy the required constraints.
obOf :: (Category (Dom f), Category (Cod f)) => NatId f -> Endo (Dom f) a
     -> Dict (Ob (Nat (Dom f) (Cod f)) f, Ob (Dom f) a, Ob (Cod f) (f a))
obOf f a = case observe f of
  Dict -> case observe a of
    Dict -> case observe (f ! a) of
      Dict -> Dict

-- | The 'Copresheaves' type represents copresheaves in a category.
type Copresheaves p = Nat p (->)

-- | The 'Presheaves' type represents presheaves in a category.
type Presheaves p = Nat (Op p) (->)

-- | This instance defines the 'Functor' instance for the 'FunctorOf' type, which is a type-level representation of a functor between two categories.
-- It requires that both the source and target categories are instances of the 'Category'' type class.
instance (Category' p, Category' q) => Functor (FunctorOf p q) where
  -- | Type synonym for the domain of a functor.
  type Dom (FunctorOf p q) = Nat p q

  -- | Type synonym for the codomain of a functor.
  type Cod (FunctorOf p q) = (:-)

  -- | Functor instance for the 'Nat' type.
  fmap Nat{} = Sub Dict

--------------------------------------------------------------------------------
-- * Bifunctors
--------------------------------------------------------------------------------
-- | Type family to extract the domain of a bifunctor.
type family NatDom (f :: (i -> j) -> (i -> j) -> *) :: (i -> i -> *) where
  NatDom (Nat p q) = p

-- | Type family to extract the codomain of a bifunctor.
type family NatCod (f :: (i -> j) -> (i -> j) -> *) :: (j -> j -> *) where
  NatCod (Nat p q) = q

-- | Type synonym to simplify accessing the domain of a bifunctor.
type Dom2 p = NatDom (Cod p)

-- | Type synonym to simplify accessing the codomain of a bifunctor.
type Cod2 p = NatCod (Cod p)

-- | Class representing a bifunctor.
class (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)
instance  (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)

-- | Functor map operation for a bifunctor.
fmap1 :: forall p a b c. (Bifunctor p, Ob (Dom p) c) => Dom2 p a b -> Cod2 p (p c a) (p c b)
fmap1 f = case ob :: Ob (Dom p) c :- FunctorOf (Dom2 p) (Cod2 p) (p c) of
  Sub Dict -> fmap f

-- | Bifunctor map operation for two domains.
bimap :: Bifunctor p => Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)
bimap f g = case observe f of
  Dict -> case observe g of
    Dict -> runNat (fmap f) . fmap1 g

-- | Type synonym to simplify accessing the opposite category of a functor.
type Opd f = Op (Dom f)

-- | Contravariant map operation for a functor.
contramap :: Functor f => Opd f b a -> Cod f (f a) (f b)
contramap = fmap . unop

-- | E-Enriched profunctors f : C -/-> D are represented by a functor of the form:
--
-- C^op -> [ D, E ]
--
-- The variance here matches Haskell's order, which means that the contravariant
-- argument comes first!

-- | Maps over both the input and output of a bifunctor using two separate functions.
--
-- This function takes an `Opd` (opposite category) morphism `Opd p b a` and a `Dom2` (domain) morphism `Dom2 p c d`,
-- and returns a `Cod2` (codomain) morphism `Cod2 p (p a c) (p b d)`.
--
-- The `dimap` function is implemented by composing the `bimap` function with the `unop` function.
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

-- | The 'Vacuous' class represents a vacuous category where all objects are the same.
class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

-- | The 'Functor' instance for 'Dict' represents a functor that maps between constraints.
instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap f Dict = case f of Sub g -> g

-- | The 'Functor' instance for 'Vacuous c' represents a functor that maps between objects in the 'c' category.
instance (Category' c, Ob c ~ Vacuous c) => Functor (Vacuous c) where
  type Dom (Vacuous c) = c
  type Cod (Vacuous c) = (:-)
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * The Category of Constraints
--------------------------------------------------------------------------------

-- | The 'Functor' instance for @(->)@.
instance Functor (:-) where
  type Dom (:-) = Op (:-)
  type Cod (:-) = Nat (:-) (->) -- copresheaves
  fmap (Op f) = Nat (. f)

-- | The 'Functor' instance for @(->) b@.
instance Functor ((:-) b) where
  type Dom ((:-) b) = (:-)
  type Cod ((:-) b) = (->)
  fmap = (.)

-- | The 'Category' instance for @(->)@.
instance Category' (:-) where
  type Ob (:-) = Vacuous (:-)
  id = Constraint.refl
  observe _ = Dict
  (.) = Constraint.trans
  unop = getOp

-- | Convert a function that requires a constraint into a morphism in the category @(->)@.
sub :: (a => Proxy a -> Dict b) -> a :- b
sub k = Sub (k Proxy)

--------------------------------------------------------------------------------
-- * Hask
--------------------------------------------------------------------------------

-- | 'Functor' instance for the function arrow (->).
instance Functor (->) where
  type Dom (->) = Op (->)
  type Cod (->) = Nat (->) (->)
  fmap (Op f) = Nat (. f)

-- | 'Functor' instance for functions with a fixed argument 'a'.
instance Functor ((->)a) where
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
  fmap = (.)

-- | 'Category'' instance for the function arrow (->).
instance Category' (->) where
  type Ob (->) = Vacuous (->)
  id x = x
  observe _ = Dict
  (.) f g x = f (g x)
  unop = getOp

--------------------------------------------------------------------------------
-- * Yoneda :: i -> [ Op i, Set ]
--------------------------------------------------------------------------------
-- | This module defines instances for the 'Functor' and 'Category'' typeclasses for the 'Yoneda' type.
-- The 'Yoneda' type represents the Yoneda embedding of a category.
-- It provides a way to lift a category into a functor category.
-- The instances defined here require that the underlying category 'p' is an instance of 'Category' and that its opposite category 'Op p' is isomorphic to 'Yoneda p'.
-- The 'Functor' instance for 'Yoneda p' lifts a morphism in the category 'p' to a natural transformation in the functor category 'Nat (Yoneda p) (->)'.
-- The 'Functor' instance for 'Yoneda p a' lifts a morphism in the Yoneda embedding of 'p' to a morphism in the category '(->)'.
-- The 'Category'' instance for 'Yoneda p' defines the identity morphism, composition of morphisms, and the 'observe' function for the Yoneda embedding of 'p'.
-- The 'Ob' associated type specifies the objects of the Yoneda embedding, which are the same as the objects of the underlying category 'p'.
-- The 'id' function lifts the identity morphism of 'p' to the Yoneda embedding.
-- The 'Op' function lifts a morphism in the Yoneda embedding to a morphism in the underlying category 'p'.
-- The 'observe' function checks if a morphism in the Yoneda embedding is an isomorphism by observing its behavior on objects.
-- The 'unop' function lifts a morphism in the Yoneda embedding to a morphism in the opposite category 'Op p'.
-- The 'op' function retrieves the underlying morphism from the lifted morphism in the Yoneda embedding.
instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f = Nat (. Op f)

-- | This instance defines the 'Functor' typeclass for the 'Yoneda' type with a specific object 'a'.
-- It lifts a morphism in the Yoneda embedding of 'p' to a morphism in the category '(->)'.
instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p a) where
  type Dom (Yoneda p a) = Yoneda p
  type Cod (Yoneda p a) = (->)
  fmap = (.)

-- | This instance defines the 'Category'' typeclass for the 'Yoneda' type.
-- It provides the identity morphism, composition of morphisms, and the 'observe' function for the Yoneda embedding of 'p'.
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

-- | The 'Functor' instance for natural transformations between categories.
instance (Category' p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Op (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Op f) = Nat (. f)

-- | The 'Functor' instance for natural transformations between categories and a specific type 'a'.
instance (Category' p, Category q) => Functor (Nat p q a) where
  type Dom (Nat p q a) = Nat p q
  type Cod (Nat p q a) = (->)
  fmap = (.)

-- | The 'Category'' instance for natural transformations between categories.
instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     -- | The identity natural transformation.
     id1 :: forall f x. (Functor f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob :: Ob p x :- Ob q (f x))
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)
   unop = getOp

-- | Create a natural transformation between categories 'p' and 'q' from a polymorphic function.
nat :: (Category p ,Category q, FunctorOf p q f, FunctorOf p q g) => (forall a. Ob p a => Endo p a -> q (f a) (g a)) -> Nat p q f g
nat k = Nat (k id)

-- | Apply a natural transformation to a morphism in category 'p'.
infixr 1 !
(!) :: Nat p q f g -> p a a -> q (f a) (g a)
Nat n ! f = case observe f of
  Dict -> n

--------------------------------------------------------------------------------
-- * Instances
--------------------------------------------------------------------------------

-- | 'Functor' instance for the tuple type '(,)'. It maps a function over the first element of the tuple.
instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat $ \(a,b) -> (f a, b)

-- | 'Functor' instance for the partially applied tuple type '(,) a'. It maps a function over the second element of the tuple.
instance Functor ((,) a) where
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  fmap f (a,b) = (a, f b)

-- | 'Functor' instance for the 'Either' type. It maps a function over the left value of the 'Either' type.
instance Functor Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)
  fmap f0 = Nat (go f0) where
    -- | Helper function that applies the function 'f' to the left value of the 'Either' type.
    go :: (a -> b) -> Either a c -> Either b c
    go f (Left a)  = Left (f a)
    go _ (Right b) = Right b

-- | 'Functor' instance for 'Either' type.
instance Functor (Either a) where
  type Dom (Either a) = (->)
  type Cod (Either a) = (->)
  fmap _ (Left a) = Left a
  fmap f (Right b) = Right (f b)

-- | Applies a natural transformation to the first component of a functor.
first :: (Functor f, Cod f ~ Nat d e, Ob d c) => Dom f a b -> e (f a c) (f b c)
first = runNat . fmap

-- | 'Functor' instance for 'Fix' type.
newtype Fix (f :: * -> * -> *) (a :: *) = In { out :: f (Fix f a) a }

instance Functor Fix where
  type Dom Fix = Nat (->) (Nat (->) (->))
  type Cod Fix = Nat (->) (->)
  fmap f = case observe f of 
    Dict -> Nat $ \ (In mu) -> In (first (first f) (runNat (runNat f) mu))

-- | 'Functor' instance for 'Fix' type with constraints on the category.
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
-- * Example: In Rel the category whose objects are sets and whose morphisms are
--  (binary) relations between sets, the empty set is the unique initial object, 
--  the unique terminal object, (and hence the unique zero object.)
--------------------------------------------------------------------------------

-- Objects in the category of relations are sets.
type ObjectRel a = Set a

-- Morphisms in the category of relations are binary relations.
type MorphismRel a b = Set (ObjectRel a , ObjectRel b)

-- The category of relations.
data Rel (a :: *) (b :: *) = Rel (MorphismRel a b)

composeRel :: Rel b c -> Rel a b -> Rel a c
composeRel (Rel r) (Rel s) = undefined -- Rel (Set.fromList [ (x, z) | (x, y) <- Set.toList s, (y', z) <- Set.toList r, y == y' ])

instance Category' Rel where
  type Ob Rel = Vacuous Rel
  id = Rel Set.empty
  (Rel r) . (Rel s) = composeRel (Rel r) (Rel s)
  observe _ = Dict

-- Define the initial object for Rel which is the empty set
instance InitialObject Rel (Set a) where
  initialArrow = Rel Set.empty

-- Define the terminal object for Rel which is the empty set
instance TerminalObject Rel (Set a) where
  terminalArrow = Rel Set.empty


testRelCategory :: IO ()
testRelCategory = do
  -- test initial object (empty set)
  let initialSet = Set.empty :: Set.Set Int
  putStrLn $ "Initial Set: " ++ show initialSet

  -- test terminal object (empty set)
  let terminalSet = Set.empty :: Set.Set Int
  putStrLn $ "Terminal Set: " ++ show terminalSet

  -- test if initial and terminal objects are indeed empty sets
  putStrLn $ "Is Initial Set empty? " ++ show (Set.null initialSet)
  putStrLn $ "Is Terminal Set empty? " ++ show (Set.null terminalSet)

  -- another examples of sets
  let set1 = Set.fromList [1,2,3,4,5] :: Set.Set Int
  let set2 = Set.fromList [6,7,8,9,10] :: Set.Set Int 

  -- check if they are intial objects
  putStrLn $ "Is Set1 an initial object? " ++ show (Set.null set1)
  putStrLn $ "Is Set2 an initial object? " ++ show (Set.null set2)

  -- check if they are terminal objects
  putStrLn $ "Is Set1 a terminal object? " ++ show (Set.null set1)
  putStrLn $ "Is Set2 a terminal object? " ++ show (Set.null set2)
  

--------------------------------------------------------------------------------
-- Any partially ordered set (P, ≤) can be interpreted as a category: 
-- the objects are the elements of P, and there is a single morphism from x to y 
-- if and only if x ≤ y. This category has an initial object if and only if 
-- P has a least element; it has a terminal object if and only if P has a greatest element.
--------------------------------------------------------------------------------

-- Objects in the category of a partially ordered set.
data ObjectPOS a = ObjectPOS a deriving (Show, Eq,Bounded,Ord)

-- Morphisms in the category of a partially ordered set.
data MorphismPOS a b = a :<=: b deriving (Show, Eq,Bounded,Ord)

-- The category of a partially ordered set.
data Poset (a :: *) (b :: *) = Poset (MorphismPOS (ObjectPOS a) (ObjectPOS b)) 

instance Category' Poset where
  type Ob Poset = Vacuous Poset
  id = undefined -- Poset ((ObjectPOS x) :<=: (ObjectPOS x))
  (Poset r ) . (Poset s ) = undefined -- | y == y' = Poset (ObjectPOS x :<=: ObjectPOS z)
                                                                                    -- | otherwise = error "Cannot compose morphisms"
  observe _ = Dict

-- instance Bounded a => Bounded (MorphismPOS (ObjectPOS a) (ObjectPOS a)) where
--   minBound = ObjectPOS minBound :<=: ObjectPOS minBound
--   maxBound = ObjectPOS maxBound :<=: ObjectPOS maxBound

-- -- -- Define the initial object for Poset
-- instance InitialObject Poset (ObjectPOS Int) where
--   initialArrow = Poset minBound

-- smallestElement :: MorphismPOS (ObjectPOS Int) (ObjectPOS Int) -> ObjectPOS Int
-- smallestElement (ObjectPOS a :<=: ObjectPOS b) = ObjectPOS (min a b)

-- -- Define the initial object for Poset.
-- instance InitialObject Poset (ObjectPOS Int) where
--   initialArrow (ObjectPOS x) = Poset (smallestElement :<=: ObjectPOS x)

-- testPosetCategory :: IO ()
-- testPosetCategory = do
--   putStrLn "Testing Poset Category (Partially Ordered Sets):"
  
--   Test initial object (empty set)
--   let initialSet = poset (initialArrow :: Poset Int Int)
--   putStrLn $ "Initial Set: " ++ show initialSet
  
--   -- Test terminal object (empty set)
--   let terminalSet = poset (terminalArrow :: Poset Int Int)
--   putStrLn $ "Terminal Set: " ++ show terminalSet
  
--   -- Check if initial and terminal objects are indeed empty sets
--   putStrLn $ "Is Initial Set empty? " ++ show (Set.null initialSet)
--   putStrLn $ "Is Terminal Set empty? " ++ show (Set.null terminalSet)
  
--------------------------------------------------------------------------------
-- In Ring, the category of rings with unity and unity-preserving morphisms,
-- the ring of integers Z is an initial object. The zero ring consisting only 
-- of a single element 0 = 1 is a terminal object.
-- --------------------------------------------------------------------------------
-- Objects in the category of rings.
data ObjectRing a 

-- Morphisms in the category of rings.
-- In the category of rings, a morphism is a ring homomorphism. 
-- A ring homomorphism is a function between two rings that preserves the ring operations, 
-- namely addition and multiplication, and the unity (identity element).
data MorphismRing a b 

-- The category of rings.
data Ring (a :: *) (b :: *) = Ring (MorphismRing (ObjectRing a) (ObjectRing b)) 

instance Category' Ring where
  type Ob Ring = Vacuous Ring
  id = undefined  
  (Ring r ) . (Ring s ) = undefined 
  observe _ = Dict

-- -- Define a typeclass for rings
-- class Ring a where
--   unity :: a
--   add :: a -> a -> a
--   mul :: a -> a -> a
--   neg :: a -> a

-- -- Define the data type for the ring of integers (initial object)
-- data Z = Z

-- -- Define Z as an instance of the Ring typeclass
-- instance Ring Z where
--   unity = Z
--   add _ _ = Z
--   mul _ _ = Z
--   neg _ = Z

-- -- Define the data type for the zero ring (terminal object)
-- data ZeroRing = ZeroRing

-- -- Define ZeroRing as an instance of the Ring typeclass
-- instance Ring ZeroRing where
--   unity = ZeroRing
--   add _ _ = ZeroRing
--   mul _ _ = ZeroRing
--   neg _ = ZeroRing

-- -- Define a data type for representing morphisms in the category of rings
-- data RingMorphism a b  -- RingMorphism { ringMorphism :: a -> b }

-- -- Define RingMorphism as an instance of Category' typeclass
-- instance Category' RingMorphism where
--   type Ob RingMorphism = Ring
--   id = RingMorphism Prelude.id
--   RingMorphism g . RingMorphism f = RingMorphism (g Prelude.. f)
--   observe _ = Dict


-- -- Define the initial object for Ring
-- instance InitialObject Ring Z where
--   initialArrow = Z

-- -- Define the terminal object for Ring
-- instance TerminalObject Ring ZeroRing where
--   terminalArrow = ZeroRing

-- testRingCategory :: IO ()
-- testRingCategory = do
--   putStrLn "Testing Ring Category:"
  
--   -- Test initial object (Z)
--   let initialRing = initialArrow :: Z
--   putStrLn $ "Initial Ring: " ++ show initialRing
  
--   -- Test terminal object (ZeroRing)
--   let terminalRing = terminalArrow :: ZeroRing
--   putStrLn $ "Terminal Ring: " ++ show terminalRing
  
--   -- Check if initial and terminal objects are indeed initial and terminal rings
--   putStrLn $ "Is Initial Ring Z? " ++ show (initialRing == Z)
--   putStrLn $ "Is Terminal Ring ZeroRing? " ++ show (terminalRing == ZeroRing)
  
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

-- Objects in the category of vector spaces.
data ObjectVectorSpace a 

-- Morphisms in the category of vector spaces.
data MorphismVectorSpace a b 

-- The category of vector spaces.
data VectorSpace (a :: *) (b :: *) = VectorSpace (MorphismVectorSpace (ObjectVectorSpace a) (ObjectVectorSpace b)) 

instance Category' VectorSpace where
  type Ob VectorSpace = Vacuous VectorSpace
  id = undefined  
  (VectorSpace r ) . (VectorSpace s ) = undefined 
  observe _ = Dict


-- Define a type for vector spaces over a scalar field 'k'
-- data VectorSpace k a = VectorSpace

-- -- Define linear transformations between vector spaces
-- data LinearMap k a b = LinearMap { linearMap :: a -> b }

-- -- Functor instance for VectorSpace
-- instance Functor (VectorSpace k) where
--   type Dom (VectorSpace k) = (->)
--   type Cod (VectorSpace k) = (->)
--   fmap _ = VectorSpace  -- Identity transformation for vector spaces

-- -- Initial object: The zero-dimensional vector space
-- instance InitialObject (LinearMap k) Void where
--   initialArrow = LinearMap absurd  -- No linear transformations from the zero vector space

-- -- Terminal object: The one-dimensional vector space
-- instance TerminalObject (LinearMap k) () where
--   terminalArrow = LinearMap (\_ -> ())  -- Unique linear transformation to the one-dimensional vector space

-- -- Product of vector spaces
-- instance Product (LinearMap k) (VectorSpace k) (VectorSpace k) (VectorSpace k) where
--   pair f g = LinearMap (\x -> (linearMap f x, linearMap g x))  -- Linear transformation combining two vector spaces
--   leftProjection = LinearMap (\(x, _) -> x)  -- Projection map to the first factor space
--   rightProjection = LinearMap (\(_, y) -> y)  -- Projection map to the second factor space

-- -- Coproduct of vector spaces
-- instance Sum (LinearMap k) (VectorSpace k) (VectorSpace k) (VectorSpace k) where
--   leftInjection = LinearMap Left  -- Injection map from the first factor space
--   rightInjection = LinearMap Right  -- Injection map from the second factor space
--   sumCase = LinearMap (either id id)  -- Unique linear transformation from the coproduct

-- -- Test function to verify vector spaces and linear transformations
-- testVectorSpaceCategory :: IO ()
-- testVectorSpaceCategory = do
--     putStrLn "Testing Vector Spaces and Linear Maps"
--     putStrLn "------------------------------------"
--     putStrLn "1. Initial and Terminal Objects:"
--     putStrLn "   Initial object should have no linear transformations:"
--     putStrLn $ "   Initial Arrow for Void: " ++ show (linearMap initialArrow :: Void -> Int)
--     putStrLn "   Terminal object should have unique linear transformation to ()"
--     putStrLn $ "   Terminal Arrow for (): " ++ show (linearMap terminalArrow :: Int -> ())
--     putStrLn ""
--     putStrLn "2. Product and Coproduct:"
--     let v1 = VectorSpace :: VectorSpace Int Int
--         v2 = VectorSpace :: VectorSpace Int Int
--         p = pair v1 v2 :: LinearMap Int (Int, Int) (Int, Int)
--         (l1, l2) = (leftProjection :: LinearMap Int (Int, Int) Int, rightProjection :: LinearMap Int (Int, Int) Int)
--         (i1, i2) = (leftInjection :: LinearMap Int Int (Either Int Int), rightInjection :: LinearMap Int Int (Either Int Int))
--         (f, g) = (linearMap l1, linearMap l2)
--         (inl, inr) = (linearMap i1, linearMap i2)
--         (sumF, sumG) = (linearMap $ sumCase :: Either Int Int -> Int, linearMap $ sumCase :: Either Int Int -> Int)
--     putStrLn $ "   Pairing of Vector Spaces (2, 3): " ++ show (linearMap p (2, 3))
--     putStrLn $ "   Left Projection of (2, 3): " ++ show (f (2, 3))
--     putStrLn $ "   Right Projection of (2, 3): " ++ show (g (2, 3))
--     putStrLn $ "   Left Injection of 5: " ++ show (inl 5)
--     putStrLn $ "   Right Injection of 7: " ++ show (inr 7)
--     putStrLn $ "   Sum Case of Left 10: " ++ show (sumF (Left 10))
--     putStrLn $ "   Sum Case of Right 20: " ++ show (sumG (Right 20))

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
--   testPosetCategory
--   testRingCategory
--   testVectorSpaceCategory
--   putStrLn "All tests passed successfully!"

