{-# LANGUAGE ExplicitForAll, ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, InstanceSigs #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE GADTSyntax, GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

-- Library imports -------------------------------------------------------------

import Data.Word (Word8)
import qualified Data.ByteString as BS

import System.Environment (getProgName, getArgs)
import System.IO (hPutStrLn, stderr)

-- Utilities normally in Control.Arrow -----------------------------------------

-- Reversed function composition
(>>>) :: forall (a :: *) (b :: *) (c :: *). (a -> b) -> (b -> c) -> (a -> c)
(>>>) = flip (.)

-- Swapping ordered pairs
swap :: forall (a :: *) (b :: *). (a, b) -> (b, a)
swap (l, r) = (r, l)

-- Applying a function to the left side of an ordered pair
left :: forall (a :: *) (b :: *) (c :: *). (a -> b) -> ((a, c) -> (b, c))
left f (l, r) = (f l, r)

-- Applying a function to the right side of an ordered pair
right :: forall (a :: *) (b :: *) (c :: *). (a -> b) -> ((c, a) -> (c, b))
right f (l, r) = (l, f r)

-- Type-level Peano arithmetic -------------------------------------------------

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

type family Add (x :: Nat) (y :: Nat) :: Nat
type instance Add 'Zero x = x
type instance Add ('Succ x) y = 'Succ (Add x y)

type One = 'Succ 'Zero
type Two = Add One One
type Three = 'Succ Two
type Four = Add Two Two
type Five = 'Succ Four
type Seven = Add Four Three
type Eight = Add Four Four
type Nine = 'Succ Eight
type Ten = Add Five Five

-- Finite types of n elements --------------------------------------------------
-- (effectively, natural numbers less than or equal to some maximum)

data Fin (n :: Nat) :: * where
  FZero :: forall (m :: Nat). Fin m
  FSucc :: forall (m :: Nat). Fin m -> Fin ('Succ m)
deriving instance Show (Fin n)

f0 :: forall (n :: Nat). Fin n
f0 = FZero
f1 :: forall (n :: Nat). Fin ('Succ n)
f1 = FSucc f0
f2 :: forall (n :: Nat). Fin ('Succ ('Succ n))
f2 = FSucc f1
f3 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ n)))
f3 = FSucc f2
f4 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ n))))
f4 = FSucc f3
f5 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ ('Succ n)))))
f5 = FSucc f4
f6 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ n))))))
f6 = FSucc f5
f7 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ n)))))))
f7 = FSucc f6
f8 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ n))))))))
f8 = FSucc f7
f9 :: forall (n :: Nat). Fin ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ ('Succ n)))))))))
f9 = FSucc f8

-- Vectors ---------------------------------------------------------------------
-- (polymorphic lists of cons cells with size encoded at the type level)

-- Representing our bit strings this way has nice properties: it is impossible
-- to have an out-of-bounds error at runtime! The compiler will force us to
-- prove that any index is within the proper bounds. This can make certain
-- things verbose, but it's the only way to formally ensure correctness.

data Vec (n :: Nat) (a :: *) :: * where
  None :: forall (a :: *). Vec 'Zero a
  Some :: forall (m :: Nat) (a :: *). a -> Vec m a -> Vec ('Succ m) a

lengthVec :: forall (n :: Nat) (a :: *). Vec n a -> Int
lengthVec None = 0
lengthVec (Some _ bs) = 1 + lengthVec bs

indexVec :: forall (n :: Nat) (a :: *). Fin n -> Vec ('Succ n) a -> a
indexVec FZero (Some b _) = b
indexVec (FSucc x) (Some _ bs) = indexVec x bs

concatVec :: forall (n :: Nat) (m :: Nat) (a :: *). Vec n a -> Vec m a -> Vec (Add n m) a
concatVec None x = x
concatVec (Some b bs) x = Some b $ concatVec bs x

popVec :: forall (n :: Nat) (a :: *). Vec ('Succ n) a -> Vec n a
popVec (Some _ bs) = bs

-- Notice that there are three split functions for different vector lenghts.
-- We cannot define a general interface for splitting arbitrary-length vectors
-- easily in Haskell, as without true dependent types it is difficult to move
-- the length parameter between the term and type levels. We could fake it
-- using a singleton type, but this would be overly verbose for this
-- assignment.
splitVec4 :: forall (a :: *). Vec Four a -> (Vec Two a, Vec Two a)
splitVec4 (Some a (Some b rest)) = (Some a $ Some b None, rest)

splitVec8 :: forall (a :: *). Vec Eight a -> (Vec Four a, Vec Four a)
splitVec8 (Some a (Some b (Some c (Some d rest)))) = (Some a . Some b . Some c $ Some d None, rest)

splitVec10 :: forall (a :: *). Vec Ten a -> (Vec Five a, Vec Five a)
splitVec10 (Some a (Some b (Some c (Some d (Some e rest))))) = (Some a . Some b . Some c . Some d $ Some e None, rest)

-- Bit strings -----------------------------------------------------------------
-- (as vectors of booleans)

type Bits n = Vec n Bool

xorBits :: forall (n :: Nat). Bits n -> Bits n -> Bits n
xorBits None None = None
xorBits (Some b bs) (Some b' bs') = Some (xor b b') $ xorBits bs bs'
  where xor :: Bool -> Bool -> Bool
        xor True False = True
        xor False True = True
        xor _ _ = False

-- Permutation tables ----------------------------------------------------------
-- (as vectors of valid indices in a source vector)

type Perm n m = Vec n (Fin m)

permuteBits :: forall (n :: Nat). Perm ('Succ n) n -> Bits ('Succ n) -> Bits ('Succ n)
permuteBits perm bs = go perm
  where getBit :: Fin n -> Bool
        getBit i = indexVec i bs
        go :: forall (m :: Nat). Perm m n -> Bits m
        go None = None
        go (Some p ps) = Some (getBit p) $ go ps

-- DES implementation ----------------------------------------------------------

-- The initial permutation
initialPermutation :: Bits Eight -> Bits Eight
initialPermutation = permuteBits table
  where table :: Perm Eight Seven
        table = Some f1 . Some f5 . Some f2 . Some f0 . Some f3 . Some f7 . Some f4 $ Some f6 None

-- Compute the value of an f-box from a given 8-bit partial key.
-- Notice how verbose the substitution tables are: given the nonlinearity of the
-- function and the details of our bitstring representation, it is easiest to
-- simply match every possibe 4-bit value. In a full DES implementation, we would
-- likely want to write the necessary conversion functions to convert arbitrary
-- bitstrings into indices in a constant vector of output values (the C way, but
-- safer), but for now, we choose to avoid writing the (verbose) type-level
-- machinery.
-- Also notice the elegance of the actual definition from its components using
-- (>>>) and left/right. Working in pointfree/concatenative style makes this
-- definition exactly mirror the diagram given in the lecture notes!
fbox :: Bits Eight -> Bits Four -> Bits Four
fbox key = expansionPermutation >>> xorBits key >>> splitVec8 >>> left substitution1 >>> right substitution2 >>> uncurry concatVec >>> finalPermutation
  where expansionPermutation :: Bits Four -> Bits Eight
        expansionPermutation bs = concatVec (permuteBits table1 bs) (permuteBits table2 bs)
          where table1 :: Perm Four Three
                table1 = Some f3 . Some f0 . Some f1 $ Some f2 None
                table2 :: Perm Four Three
                table2 = Some f1 . Some f2 . Some f3 $ Some f0 None
        substitution1 :: Bits Four -> Bits Two
        substitution1 (Some False (Some False (Some False (Some False None)))) = Some False $ Some True None
        substitution1 (Some False (Some False (Some False (Some True None))))  = Some True  $ Some True None
        substitution1 (Some False (Some False (Some True (Some False None))))  = Some False $ Some False None
        substitution1 (Some False (Some False (Some True (Some True None))))   = Some True  $ Some False None
        substitution1 (Some False (Some True (Some False (Some False None))))  = Some True  $ Some True None
        substitution1 (Some False (Some True (Some False (Some True None))))   = Some False $ Some True None
        substitution1 (Some False (Some True (Some True (Some False None))))   = Some True  $ Some False None
        substitution1 (Some False (Some True (Some True (Some True None))))    = Some False $ Some False None
        substitution1 (Some True (Some False (Some False (Some False None))))  = Some False $ Some False None
        substitution1 (Some True (Some False (Some False (Some True None))))   = Some True  $ Some True None
        substitution1 (Some True (Some False (Some True (Some False None))))   = Some True  $ Some False None
        substitution1 (Some True (Some False (Some True (Some True None))))    = Some False $ Some True None
        substitution1 (Some True (Some True (Some False (Some False None))))   = Some False $ Some True None
        substitution1 (Some True (Some True (Some False (Some True None))))    = Some True  $ Some True None
        substitution1 (Some True (Some True (Some True (Some False None))))    = Some True  $ Some True None
        substitution1 (Some True (Some True (Some True (Some True None))))     = Some True  $ Some False None
        substitution2 :: Bits Four -> Bits Two
        substitution2 (Some False (Some False (Some False (Some False None)))) = Some False $ Some False None
        substitution2 (Some False (Some False (Some False (Some True None))))  = Some True  $ Some False None
        substitution2 (Some False (Some False (Some True (Some False None))))  = Some False $ Some True None
        substitution2 (Some False (Some False (Some True (Some True None))))   = Some False $ Some False None
        substitution2 (Some False (Some True (Some False (Some False None))))  = Some True  $ Some False None
        substitution2 (Some False (Some True (Some False (Some True None))))   = Some False $ Some True None
        substitution2 (Some False (Some True (Some True (Some False None))))   = Some True  $ Some True None
        substitution2 (Some False (Some True (Some True (Some True None))))    = Some True  $ Some True None
        substitution2 (Some True (Some False (Some False (Some False None))))  = Some True  $ Some True None
        substitution2 (Some True (Some False (Some False (Some True None))))   = Some True  $ Some False None
        substitution2 (Some True (Some False (Some True (Some False None))))   = Some False $ Some False None
        substitution2 (Some True (Some False (Some True (Some True None))))    = Some False $ Some True None
        substitution2 (Some True (Some True (Some False (Some False None))))   = Some False $ Some True None
        substitution2 (Some True (Some True (Some False (Some True None))))    = Some False $ Some False None
        substitution2 (Some True (Some True (Some True (Some False None))))    = Some False $ Some False None
        substitution2 (Some True (Some True (Some True (Some True None))))     = Some True  $ Some True None
        finalPermutation :: Bits Four -> Bits Four
        finalPermutation = permuteBits table
          where table :: Perm Four Three
                table = Some f1 . Some f3 . Some f2 $ Some f0 None

-- A single round of Feistel transformation given an 8-bit partial key.
feistel :: Bits Eight -> (Bits Four, Bits Four) -> (Bits Four, Bits Four)
feistel key (l, r) = (r, xorBits l (fbox key r))

-- The final permutation ("undoing" the initial permutation).
inverseInitialPermutation :: Bits Eight -> Bits Eight
inverseInitialPermutation = permuteBits table
  where table :: Perm Eight Seven
        table = Some f3 . Some f0 . Some f2 . Some f4 . Some f6 . Some f1 . Some f7 $ Some f5 None

-- Perform DES given the 8-bit two partial keys.
-- This allows us to abstract the common details of encryption and decryption,
-- which only differ in the order of the partial keys.
doDES :: (Bits Eight, Bits Eight) -> Bits Eight -> Bits Eight
doDES (k1, k2) = initialPermutation >>> splitVec8 >>> feistel k1 >>> feistel k2 >>> swap >>> uncurry concatVec >>> inverseInitialPermutation

-- Compute the two 8-bit partial keys from a full 10-bit key.
splitKey :: Bits Ten -> (Bits Eight, Bits Eight)
splitKey key = (left (uncurry concatVec >>> key8Permutation) >>> right (left rotateLeft >>> right rotateLeft >>> uncurry concatVec >>> key8Permutation)) (fives, fives)
  where fives = (key10Permutation >>> splitVec10 >>> left rotateLeft >>> right rotateLeft) key
        key10Permutation :: Bits Ten -> Bits Ten
        key10Permutation = permuteBits table
          where table :: Perm Ten Nine
                table = Some f2 . Some f4 . Some f1 . Some f6 . Some f3 . Some f9 . Some f0 . Some f8 . Some f7 $ Some f5 None
        key8Permutation :: Bits Ten -> Bits Eight
        key8Permutation = popVec >>> popVec >>> permuteBits table
          where table :: Perm Eight Seven
                table = Some f3 . Some f0 . Some f4 . Some f1 . Some f5 . Some f2 . Some f7 $ Some f6 None 
        rotateLeft :: Bits Five -> Bits Five
        rotateLeft (Some b bs) = concatVec bs (Some b None)

-- Helper for performing encryption of a byte given a 10-bit key.
encryptDES :: Bits Ten -> Bits Eight -> Bits Eight
encryptDES = splitKey >>> doDES

-- Helper for performing decryption of a byte given a 10-bit key.
-- As previously mentioned, the only difference is swapping the partial keys!
decryptDES :: Bits Ten -> Bits Eight -> Bits Eight
decryptDES = splitKey >>> swap >>> doDES

-- Command-line interface ------------------------------------------------------

-- Convert an 8-bit bit string to a Haskell integer.
bitsToInt :: Bits Eight -> Int
bitsToInt bits = go (lengthVec bits - 1) bits
  where go :: forall (n :: Nat). Int -> Bits n -> Int
        go _ None = 0
        go l (Some b bs) = (if b then 1 else 0) * 2^l + go (l - 1) bs

-- Convert a Haskell integer to an 8-bit bit string.
-- If the Haskell integer is greater than 255, use the highest 8 bits.
intToBits :: Int -> Bits Eight
intToBits = extract . pad . reverse . rep
  where rep :: Int -> [Bool]
        rep 0 = []
        rep n = (rem n 2 == 1):rep (quot n 2)
        pad :: [Bool] -> [Bool]
        pad l | length l >= 8 = l
              | otherwise = pad (False:l)
        extract :: [Bool] -> Bits Eight
        extract (b1:b2:b3:b4:b5:b6:b7:b8:_) = Some b1 . Some b2 . Some b3 . Some b4 . Some b5 . Some b6 . Some b7 $ Some b8 None
        extract _ = error "Invalid byte"

-- Create a 10-bit bitstring (a key) from a Haskell string of '1' and '0'.
buildKey :: String -> Bits Ten
buildKey = extract . fmap (=='1')
  where extract :: [Bool] -> Bits Ten
        extract (b1:b2:b3:b4:b5:b6:b7:b8:b9:b10:_) = Some b1 . Some b2 . Some b3 . Some b4 . Some b5
                                                     . Some b6 . Some b7 . Some b8 . Some b9 $ Some b10 None
        extract _ = error "Invalid key"

-- Encrypt a single byte using the given key.
encryptByte :: String -> Word8 -> Word8
encryptByte key = fromIntegral . bitsToInt . encryptDES (buildKey key) . intToBits . fromIntegral

-- Decrypt a single byte using the given key.
decryptByte :: String -> Word8 -> Word8
decryptByte key = fromIntegral . bitsToInt . decryptDES (buildKey key) . intToBits . fromIntegral

-- Encrypt an entire bytestring using the given key.
encryptByteString :: String -> BS.ByteString -> BS.ByteString
encryptByteString key = BS.map (encryptByte key)

-- Decrypt an entire bytestring using the given key.
decryptByteString :: String -> BS.ByteString -> BS.ByteString
decryptByteString key = BS.map (decryptByte key)

main :: IO ()
main = do
  prog <- getProgName
  args <- getArgs
  case args of
    "encrypt":cargs ->
      case cargs of
        key:_ -> encryptByteString key <$> BS.getContents >>= BS.putStr
        _ -> hPutStrLn stderr $ mconcat ["Usage: ", prog, " encrypt <key>"]
    "decrypt":cargs ->
      case cargs of
        key:_ -> decryptByteString key <$> BS.getContents >>= BS.putStr
        _ -> hPutStrLn stderr $ mconcat ["Usage: ", prog, " decrypt <key>"]
    _ -> hPutStrLn stderr $ mconcat ["Usage: ", prog, " <command> [<args>]"]
  pure ()
