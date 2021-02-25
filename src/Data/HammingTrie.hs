{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE OverloadedLabels #-}

module Data.HammingTrie
    ( Trie
    , TrieKey(..)
    , insert
    , findNear
    , find
    , findNearWithKey
    , findWithKey
    -- XXX implement the below
    -- , deleteNear
    -- , delete
    ) where

import Data.List (foldl')
import Data.Vector (Vector,(!?))
import qualified Data.Vector as V
import Data.Maybe (listToMaybe)

class TrieKey k where
    type Bucket k = t | t -> k -- :: *
    compareBin :: Bucket k -> Bucket k -> Ordering
    default compareBin :: (Ord (Bucket k)) => Bucket k -> Bucket k -> Ordering
    compareBin = compare
    combineKey :: Bucket k -> k -> k
    splitKey :: k -> Maybe (Bucket k, k)
    emptyKey :: k

instance TrieKey [Bool] where
    type Bucket [Bool] = Bool
    combineKey = (:)
    splitKey [] = Nothing
    splitKey (x:xs) = Just (x,xs)
    emptyKey = []

type TrieConstr k b = (b ~ Bucket k, Ord b, TrieKey k, Eq k, Eq b)
type TrieConstrD k b = (b ~ Bucket k, Ord b, TrieKey k)

data Trie k b a
    = Node  (Maybe a) (Vector (b,Trie k b a))
    | Leaf  (Maybe k) a
 deriving (Eq,Ord,Show)

node :: Maybe a -> Vector (b, Trie k b a) -> Trie k b a
node a v = v `seq` Node a v

leaf :: Maybe k -> a -> Trie k b a
leaf Nothing a = Leaf Nothing a
leaf k@(Just x) a = x `seq` Leaf k a

instance (Eq k, TrieConstrD k b) => Monoid (Trie k b a) where
    mempty = Node Nothing V.empty

instance (Eq k, TrieConstrD k b) => Semigroup (Trie k b a) where
    (<>) l r = foldl' (\t (k,a) -> insert k a t) l (toList r)

toList :: (TrieConstrD k b) => Trie k b a -> [(k,a)]
toList (Node (Just v) xs) = (emptyKey,v) : mconcat (pairList <$> V.toList xs)
toList (Node Nothing xs) = mconcat (pairList <$> V.toList xs)
toList (Leaf (Just k) a) = [(k,a)]
toList (Leaf Nothing a)  = [(emptyKey,a)]

pairList :: (TrieConstrD k b) => (b,Trie k b a) -> [(k,a)]
pairList (b,t) = (\(k,v) -> (combineKey b k, v)) <$> toList t

-- instance (TrieConstr k b) => Traversable (Trie k b d) where
--     ...
-- instance (TrieConstr k b) => Foldable (Trie k b d) where
--     ...

binKey :: TrieConstr k b => k -> b -> a -> Vector (b,Trie k b a) -> Vector (b, Trie k b a)
binKey subKey b val bs =
  let ix = bSearch b bs
      ls = V.take ix bs
      rs = V.drop ix bs
      newChild = insert subKey val mempty
  in case (bs !? ix) of
        Just (bin,child) | bin == b  ->
                        -- Mutate existing child
                        let modChild = insert subKey val child
                        in modChild `seq` (ls <> [(b,modChild)] <> V.drop 1 rs)
                 | otherwise ->
                         -- New child in middle
                         newChild `seq` (ls <> [(b,newChild)] <> rs)
        Nothing    -> -- New child at end
                      newChild `seq` (bs <> [(b,  newChild)])

bSearch :: TrieConstr k b => b -> Vector (b,x) -> Int
bSearch b v | V.length v == 0 = 0
            | otherwise =
  let go l r | l >= r                       = r
             | compareBin b (fst $ v V.! m) /= GT = go l m
             | otherwise                    = go (m+1) r
         where m = (l + r) `div` 2
  in go 0 (max (V.length v) 1)

insert :: TrieConstr k b => k -> val -> Trie k b val -> Trie k b val
insert k val (Node Nothing children) | V.length children == 0 = Leaf (Just k) val
insert k val (Node mv children) =
    case splitKey k of
        Just (b,subKey)
            | V.length children > 0 -> Node mv (binKey subKey b val children)
            | otherwise -> Node mv [(b,Leaf (Just subKey) val)]
        Nothing -> Node (Just val) children
insert k val (Leaf (Just oldKey) oldVal)
    | k == oldKey = Leaf (Just k) val
    | otherwise =
    case splitKey oldKey of
        Nothing -> insert k val (Leaf Nothing oldVal)
        Just (oldB,oldSubKey) -> insert k val (Node Nothing [(oldB,Leaf (Just oldSubKey) oldVal)])
insert k val (Leaf Nothing a) =
    case splitKey k of
        Nothing -> Leaf Nothing val -- overwrite prior value
        Just (b,subKey) -> Node (Just val) [(b,insert subKey val mempty)]

findNear :: TrieConstr k b => k -> Int -> Trie k b val -> [val]
findNear _ x _ | x < 0 = []
findNear k !maxDistance (Node mv children) =
    case splitKey k of
        Just (b,subKey) ->
            let fuzzyResults = do
                    child <- snd <$> V.toList children
                    findNear subKey (maxDistance-1) child
            in case children V.!? bSearch b children of
                Just (b',subTrie) | b' == b         ->
                                     (findNear subKey maxDistance subTrie) <>
                                        mconcat [ findNear subKey (maxDistance - 1) nonMatchTrie
                                                | (bOther,nonMatchTrie) <- V.toList children
                                                , b /= bOther
                                                ]
                                        -- findNear subKey (maxDistance - 1) nonMatchTrie
                                  | otherwise       -> fuzzyResults
                Nothing -> error "Impossible, bSearch returned out of bounds."
        Nothing ->
            case mv of
               Nothing -> []
               Just x  -> [x]
findNear k !maxDistance (Leaf Nothing _) =
    [] -- Partial matches are not partial in length
findNear k !maxDistance (Leaf (Just kMatch) val) =
    let go d k1 k2 =
            case (splitKey k1, splitKey k2) of
                (Nothing,Nothing) -> [val]
                (Nothing,_)       ->  []
                (_,Nothing)       ->  []
                (Just (b1,subKey1), Just (b2,subKey2))
                    | b1 == b2  -> go d subKey1 subKey2
                    | d > 0     -> go (d-1) subKey1 subKey2
                    | otherwise -> []
    in go maxDistance k kMatch

find :: TrieConstr k b => k -> Trie k b val -> Maybe val
find k = listToMaybe . findNear k 0

findNearWithKey :: (TrieConstr k b) => k -> Int -> Trie k b val -> [(k,val)]
findNearWithKey = findNearWithKey' []

findNearWithKey' :: (TrieConstr k b) => [b] -> k -> Int -> Trie k b val -> [(k,val)]
findNearWithKey' _ _ x _ | x < 0 = []
findNearWithKey' kPrior k !maxDistance (Node mv children) =
    case splitKey k of
        Just (b,subKey) ->
            case children V.!? bSearch b children of
                Just (b',subTrie) | b' == b && maxDistance == 0 ->
                    findNearWithKey' (b:kPrior) subKey 0 subTrie
                                  | otherwise ->
                                     mconcat [ findNearWithKey' (bOther:kPrior) subKey (maxDistance - diff) nonMatchTrie
                                             | (bOther,nonMatchTrie) <- V.toList children
                                             , let diff = if b == bOther then 0 else 1
                                             ]
                Nothing -> error "Impossible, bSearch returned out of bounds."
        Nothing ->
            case mv of
               Nothing -> []
               Just x  -> [(combinePriors kPrior,x)]
findNearWithKey' kPrior k !_maxDistance (Leaf Nothing val) =
    case splitKey k of
        Nothing -> [(combinePriors kPrior,val)]
        Just _  -> [] -- Partial matches are not partial in length
findNearWithKey' kPrior k !maxDistance (Leaf (Just kMatch) val) =
    let go d kP k1 k2 =
            case (splitKey k1, splitKey k2) of
                (Nothing,Nothing) -> [(combinePriors kP,val)]
                (Nothing,_)       ->  []
                (_,Nothing)       ->  []
                (Just (b1,subKey1), Just (b2,subKey2))
                    | b1 == b2  -> go d (b2:kP) subKey1 subKey2
                    | d > 0     -> go (d-1) (b2:kP) subKey1 subKey2
                    | otherwise -> []
    in go maxDistance kPrior k kMatch

combinePriors :: TrieConstrD k b => [b] -> k
combinePriors = foldr combineKey emptyKey . reverse

findWithKey :: (TrieConstr k b) => k -> Trie k b val -> [(k,val)]
findWithKey k = findNearWithKey k 0
