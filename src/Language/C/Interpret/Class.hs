{-# LANGUAGE MultiParamTypeClasses #-}

module Language.C.Interpret.Class (
    OrdInterpretation(..),
    IntInterpretation(..),
    Interpretation(..),
) where

import Data.Bits

class OrdInterpretation t int where
    (.<) :: t -> t -> int
    (.>) :: t -> t -> int
    (.<=) :: t -> t -> int
    (.>=) :: t -> t -> int
    (.==) :: t -> t -> int
    (./=) :: t -> t -> int

class IntInterpretation int where
    (./) :: int -> int -> int
    (.%) :: int -> int -> int
    (.<<) :: int -> int -> int
    (.>>) :: int -> int -> int
    (.&) :: int -> int -> int
    (.|) :: int -> int -> int
    (.^) :: int -> int -> int
    (.~) :: int -> int
    (.!) :: int -> int
    (.&&) :: int -> int -> int
    (.||) :: int -> int -> int

class (Num int, OrdInterpretation int int, IntInterpretation int, Fractional float, OrdInterpretation float int, Read float) => Interpretation int float where
    intToFloat :: int -> float

fromBool :: Num b => (a -> a -> Bool) -> a -> a -> b
fromBool f a b = if f a b then 1 else 0

instance OrdInterpretation Integer Integer where
    (.<) = fromBool (<)
    (.>) = fromBool (>)
    (.<=) = fromBool (<=)
    (.>=) = fromBool (>=)
    (.==) = fromBool (==)
    (./=) = fromBool (/=)

instance OrdInterpretation Double Integer where
    (.<) = fromBool (<)
    (.>) = fromBool (>)
    (.<=) = fromBool (<=)
    (.>=) = fromBool (>=)
    (.==) = fromBool (==)
    (./=) = fromBool (/=)

instance IntInterpretation Integer where
    (./) = div
    (.%) = mod
    (.<<) a b = a `shiftL` fromInteger b
    (.>>) a b = a `shiftR` fromInteger b
    (.&) = (.&.)
    (.|) = (.|.)
    (.^) = xor
    (.~) = complement
    (.!) v = if v == 0 then 1 else 0
    (.&&) = fromBool (\ a b -> a /= 0 && b /= 0)
    (.||) = fromBool (\ a b -> a /= 0 || b /= 0)

instance Interpretation Integer Double where
    intToFloat = realToFrac
