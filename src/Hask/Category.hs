{-# LANGUAGE CPP, KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, DefaultSignatures, NoMonomorphismRestriction #-}
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
import Prelude (($), Either(..))

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

--InitialObject
data InitialObject a where
  InitialMorphism :: Ob p a => InitialObject a

instance Functor InitialObject where
  type Dom InitialObject = p
  type Cod InitialObject = (:-)
  fmap _ = Sub Dict

instance Category' InitialObject where
  type Ob InitialObject = Vacuous InitialObject
  id = InitialMorphism
  observe _ = Dict
  (.) _ _ = InitialMorphism
  unop = getOp

--TerminalObject
data TerminalObject a where
  TerminalMorphism :: Ob p a => TerminalObject a

instance Functor TerminalObject where
  type Dom TerminalObject = p
  type Cod TerminalObject = (:-)
  fmap _ = Sub Dict

instance Category' TerminalObject where
  type Ob TerminalObject = Vacuous TerminalObject
  id = TerminalMorphism
  observe _ = Dict
  (.) _ _ = TerminalMorphism
  unop = getOp



-- Example usage
demoInitTerm :: IO ()
demoInitTerm = do
  let initialObjectInstance :: InitialObject Int
      initialObjectInstance = InitialMorphism

  -- Use the initial object
  case observe initialObjectInstance of
    Dict -> putStrLn "Initial object is observed in the category"

  let terminalObjectInstance :: TerminalObject Int
      terminalObjectInstance = TerminalMorphism
   -- Use the terminal object
  case observe terminalObjectInstance of
    Dict -> putStrLn "Terminal object is observed in the category"


--------------------------------------------------------------------------------
-- * Example: In the category Rel of sets and relations, the empty set is the 
--   unique initial object, the unique terminal object, (and hence the unique 
--   zero object.)
--------------------------------------------------------------------------------

-- Example usage in the category of sets and relations (Rel)
type Set = [Int]  -- Simplified representation of sets

instance Ob InitialObject Set
instance Ob TerminalObject Set

-- Example usage
demoRel :: IO ()
demoRel = do
  let initialObjectInstance :: InitialObject Set
      initialObjectInstance = InitialMorphism

      terminalObjectInstance :: TerminalObject Set
      terminalObjectInstance = TerminalMorphism

  putStrLn "Initial Object:"
  case observe initialObjectInstance of
    Dict -> putStrLn "Empty set is the unique initial object."

  putStrLn "\nTerminal Object:"
  case observe terminalObjectInstance of
    Dict -> putStrLn "Empty set is the unique terminal object."

--------------------------------------------------------------------------------
-- Any partially ordered set (P, ≤) can be interpreted as a category: 
-- the objects are the elements of P, and there is a single morphism from x to y 
-- if and only if x ≤ y. This category has an initial object if and only if 
-- P has a least element; it has a terminal object if and only if P has a greatest element.
--------------------------------------------------------------------------------

-- Example usage in the category of partially ordered sets (Poset)
type PosetElement = Int  -- Simplified representation of elements in the poset

instance Ob InitialObject PosetElement
instance Ob TerminalObject PosetElement

-- Function to demonstrate the uniqueness of initial and terminal objects in a poset
demoPoset :: IO ()
demoPoset = do
  let initialObjectInstance :: InitialObject PosetElement
      initialObjectInstance = InitialMorphism

      terminalObjectInstance :: TerminalObject PosetElement
      terminalObjectInstance = TerminalMorphism

  putStrLn "Initial Object (Least Element):"
  case observe initialObjectInstance of
    Dict -> putStrLn "The initial object corresponds to the least element in the poset."

  putStrLn "\nTerminal Object (Greatest Element):"
  case observe terminalObjectInstance of
    Dict -> putStrLn "The terminal object corresponds to the greatest element in the poset."


--------------------------------------------------------------------------------
-- In Ring, the category of rings with unity and unity-preserving morphisms,
-- the ring of integers Z is an initial object. The zero ring consisting only 
-- of a single element 0 = 1 is a terminal object.
--------------------------------------------------------------------------------

-- Example usage in the category of rings with unity and unity-preserving morphisms
type RingElement = Int  -- Simplified representation of ring elements

-- Ring data type with unity
data Ring a = Ring { unity :: a, addition :: a -> a -> a, multiplication :: a -> a -> a }

instance Ob InitialObject (Ring RingElement)
instance Ob TerminalObject (Ring RingElement)

-- Function to demonstrate the uniqueness of initial and terminal objects in the category of rings
demoRings :: IO ()
demoRings = do
  let initialObjectInstance :: InitialObject (Ring RingElement)
      initialObjectInstance = InitialMorphism

      terminalObjectInstance :: TerminalObject (Ring RingElement)
      terminalObjectInstance = TerminalMorphism

  putStrLn "Initial Object (Ring of Integers Z):"
  case observe initialObjectInstance of
    Dict -> putStrLn "The initial object corresponds to the ring of integers Z."

  putStrLn "\nTerminal Object (Zero Ring):"
  case observe terminalObjectInstance of
    Dict -> putStrLn "The terminal object corresponds to the zero ring."

--------------------------------------------------------------------------------
-- * Sum & Product
--------------------------------------------------------------------------------

-- Define a data type representing the sum object
data SumObject a b where
  Inl :: Ob p a => SumObject a b
  Inr :: Ob p b => SumObject a b

instance Functor (SumObject a) where
  type Dom (SumObject a) = p
  type Cod (SumObject a) = (:-)
  fmap _ = Sub Dict

instance Category' (SumObject a) where
  type Ob (SumObject a) = Vacuous (SumObject a)
  id = Inl
  observe _ = Dict
  (.) Inl _ = Inl
  (.) Inr _ = Inr
  (.) _ _ = Inl  -- Composition with Inr is not defined

-- Define a data type representing the product object
data ProductObject a b where
  Pair :: (Ob p a, Ob p b) => ProductObject a b

instance Functor (ProductObject a) where
  type Dom (ProductObject a) = p
  type Cod (ProductObject a) = (:-)
  fmap _ = Sub Dict

instance Category' (ProductObject a) where
  type Ob (ProductObject a) = Vacuous (ProductObject a)
  id = Pair
  observe _ = Dict
  (.) Pair _ = Pair


-- Example usage in the category of types and functions
type TypeObject = TypeRep  -- Simplified representation of types

-- Sum types
data EitherObj a b where
  LeftObj :: TypeObject a => EitherObj a b
  RightObj :: TypeObject b => EitherObj a b

-- Product types
data PairObj a b where
  PairObj :: (TypeObject a, TypeObject b) => PairObj a b

-- Function to demonstrate sums and products in the category of types and functions
demoSP :: IO ()
demoSP = do
  putStrLn "Sum Object (Either):"
  case observe (Inl :: SumObject (EitherObj Int Bool) (EitherObj Char Double)) of
    Dict -> putStrLn "Inl corresponds to LeftObj."

  case observe (Inr :: SumObject (EitherObj Int Bool) (EitherObj Char Double)) of
    Dict -> putStrLn "Inr corresponds to RightObj."

  putStrLn "\nProduct Object (Pair):"
  case observe (Pair :: ProductObject (PairObj Int Char) (PairObj Bool Double)) of
    Dict -> putStrLn "Pair corresponds to PairObj."