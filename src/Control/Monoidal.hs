{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies#-}
{-#  LANGUAGE TypeOperators, ScopedTypeVariables,GADTs, RankNTypes #-}
{-# LANGUAGE EmptyCase#-}

module Control.Monoidal where

import Control.Category as C
import Prelude hiding (uncurry,curry,sum)
import qualified Prelude as P
import Data.Void
{-
conal elliot  "concat"
hs -> "any cartesian closed category"

symmetric monoidal category
-}
{-
infixr 9 .
infixr 1 >>>, <<<

-- | A class for categories.
--   id and (.) must form a monoid.
class Category cat where
    -- | the identity morphism
    id :: cat a a

    -- | morphism composition
    (.) :: cat b c -> cat a b -> cat a c
-}

{-
Pair / Tuple / product ---

Sum / coproduct/ either

Choice / "external choice"

par  "a par b" == "(A -> Empty , B-> Empty) -> Empty"

-}



class Category cat => ProductCategory cat pair | cat -> pair where
  curry :: (pair a b `cat` c ) -> (a `cat` (b `cat` c))
      -- (pair a b ) `cat` (a `cat` (b `cat` c)) `cat` c
  uncurry :: (a `cat` (b `cat` c)) -> (pair a b `cat` c )
  pairMap :: (a `cat` c) -> (b `cat` d) -> (pair a b `cat` (pair c d))

class Category cat
  => SumCategory cat sum | cat -> sum where
  --sum2Choice  ::  ChoiceCategory cat choice =>
  --    (sum a b `cat`  c) ->
  --    ((choice (a `cat` c)   (b `cat` c))
  --        `cat` c )
  caseSum :: ChoiceCategory cat choice => sum a b `cat` (choice (a `cat` c) (b `cat` c)  `cat` c)
  inLeft :: a `cat` sum a b
  inRight :: b `cat` sum a b

  ---
  --sumIntro ::
{-
not (Sum a b) == choice (not a) (not b)
not (Pair a b) == par (not a) (not b)

not (choice a b) == sum (not a)

-}

type Two = Bool

class (Category cat) => ChoiceCategory cat choice | cat -> choice where
  choiceIntro ::  SumCategory cat sum  =>
        ((sum a  b )  `cat` c ) ->  (choice (a `cat` c) (b `cat` c) )
  chooseLeft :: choice a b `cat` a
  chooseRight :: choice a b `cat` b


{-
not (a,b) == par (not a) ( not b )
-}

instance ProductCategory (->) (,) where
    curry = P.curry
    uncurry = P.uncurry
    pairMap f g (a,b) = (f a, g b)


data ChooseH a b c where
  CLeft :: ChooseH a b a
  CRight :: ChooseH a b b

newtype Choice a b = MkC (forall res . ChooseH a b res -> res )
{-
see https://www.reddit.com/r/haskell/comments/4aju8f/simple_example_of_emulating_copattern_matching_in/
for more examples of this style of copattern matching encoding in haskell
(its great for coinductive descriptions)
-}

instance ChoiceCategory (->) Choice where
  chooseRight (MkC f) = f CRight
  chooseLeft (MkC f)  = f CLeft
  choiceIntro  f =  MkC $ \ x ->
          case x  of
{- cant change this to \x -> f x  or f? with ghc type checking -}
            CRight -> f C.. inRight
            CLeft -> f C.. inLeft



instance SumCategory (->)  Either where
  inLeft = Left
  inRight = Right
  caseSum elr c = case elr of
              Left a -> chooseLeft c $ a
              Right b -> chooseRight c $ b

{-

reassociate ::  Pair a (Pair b c) -> Pair (Pair a b) c
swap :: Pair a b -> Pair b a


-}


data LittleLinear a where
  LInRight ::LittleLinear (Choice  a b -> b)
  LInLEft :: LittleLinear (Choice a b -> a )
  Apply :: (LittleLinear (a -> b))-> (LittleLinear a) -> LittleLinear (b)
{-
gammas are "linear context"
   choose[a-> c,b->c] ->

not (sum a b) = choose (not a) (not b)

Gamma |-  a   Gamma |- b
-------------------------- Intro
Gamma |- choose[a,b]


Gamma |- choose[a,b]
--------------------- left elim
Gamma |- a


Gamma |- choose[a,b]
-------------------- right elim
Gamma |- b



Aside : sequent logic if you look it up,
  comma on the left of |- == "AND"
  comma on the right of |- == "OR"



PAIR Tuple
Gamma,a,b |- c
-------------- curry/uncurry
gamma, (a,b) |- c

Gamma,a |- c
------------- InLeft / left elim
Gamma, (sum a  b) |- c


Gamma,b|-  c
--------------- InRight / right elim
gamma,(sum a b)|- c


-----
Par

Not (A and B) == (Not a) Par (not b)

(direct style)
a Par b ===  (not a -> b) CHOICE (not b -> a )



OR (CPS encoding)

not not (a par b) == Not ((Not a) AND  (Not b) )
                  ==  (A -> False, B -> False ) -> False
                    "aka " a continuation that takes two continuations and uses both
--- THIS IS LIKE A CPS thread FORK for state tokens! State# RealWorld# as A and B

lets try the answer type encoding for Not

direct:
ML style
a Par b === forall c . ((a -> c) -> b) choice ((b-> c) -> a )

Rank2 style
a par b ==  ((forall c . a -> c) -> b) choice ((forall . b -> c) -> a )


lets now write the deduction rules for PAR
(remember that comma on the right in sequent notation means OR, )

Gamma |- a,b
--------------  Sequent intro rule for par in positive position
gamma |- Par a b

Gamma, not a, not b |-
--------------------------- negative position
gamma, not (Par a b)

but I dont like these sequent approaches

-}

class Category cat => AbsurdCategory cat empty | cat -> empty where
    absurdCat :: empty `cat` a

instance AbsurdCategory (->) Void where
  absurdCat x = case x of {}
  -- this exactly matching the empty sum and the empty choice!

class (Category cat) => ParCategory cat par | cat -> par where

{-
Design question: does it make sense to require both Direct and CPS par
be admissible?

NOTE WELL (Nota bene): the choice operation is implicit in the CPS encoding
because you *choose* which continuation is your "local" computation
-}
  parViaChoiceIntroForall ::  (ChoiceCategory cat choose, AbsurdCategory cat empty ) =>
      (choose ((b `cat` empty) `cat` a)
              ((a `cat` empty) `cat` b  )
              )
        -> (par a b)
  parIntroViaCPS :: (ProductCategory cat pair, AbsurdCategory cat empty) =>
          ((pair (a `cat` empty) (b `cat` empty )) `cat` empty) -> par a b
  parElimLeftForall  :: AbsurdCategory cat empty => (b `cat` empty) `cat` (par a b `cat`  a)
  parElimRightForall :: AbsurdCategory cat empty => (a `cat` empty)  `cat` (par a b `cat` b)


{-aside

if invoking par is sometimes forkIO



-}

data SimplePar  a b where
    DirectPar :: ( (a -> Void) -> b) -> ((b -> Void)-> a) -> SimplePar a b
    CPSPar :: ( ( a -> Void , b -> Void ) -> Void) -> SimplePar a b


class Category cat => SymmetricCategory cat binaryOp | binaryOp -> cat where
  swap :: (a `binaryOp` b) `cat` (b `binaryOp` a)
  reassociateRight :: ((a `binaryOp` b) `binaryOp` c ) `cat`  (a `binaryOp` (b `binaryOp` c))
  reassociateLeft :: (a `binaryOp` (b `binaryOp` c)) `cat` ((a `binaryOp` b) `binaryOp` c )
























