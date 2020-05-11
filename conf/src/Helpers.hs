{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--no-pattern-inline" @-}

module Helpers where

import           Data.Text                      ( Text
                                                , pack
                                                )
import           Database.Persist.Sql           ( fromSqlKey
                                                , ToBackendKey
                                                , SqlBackend
                                                )
import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Model
import           Controllers

{-@ pc :: u: Entity User -> TaggedT<{\_ -> True}, {\_ -> False}> _ {v: Bool | v <=> IsPc u} @-}
pc :: Monad m => Entity User -> TaggedT m Bool
pc user = do
  level <- project userLevel' user
  return (level == "chair" || level == "pc")

{-@ chair :: u: Entity User -> TaggedT<{\_ -> True}, {\_ -> False}> _ {v: Bool | v <=> IsChair u} @-}
chair :: Monad m => Entity User -> TaggedT m Bool
chair user = do
  level <- project userLevel' user
  return (level == "chair")

{-@ checkPcOr :: _ -> u:_ -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ {v: () | IsPc u} @-}
checkPcOr :: Response -> Entity User -> Controller ()
checkPcOr response user = do
  level <- project userLevel' user
  if (level == "chair" || level == "pc") then return () else respondTagged response

{-@ checkStageOr :: _ -> s:_  -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ {v: () | s == currentStage} @-}
checkStageOr :: Response -> String -> Controller ()
checkStageOr response stage = if currentStage == stage then return () else respondTagged response

outerJoinBy :: Eq key => (a -> key) -> (b -> key) -> (a -> Maybe b -> c) -> [a] -> [b] -> [c]
outerJoinBy xsKey ysKey f xs ys =
  let ysByKey = map (\y -> (ysKey y, y)) ys in map (\x -> f x (lookup (xsKey x) ysByKey)) xs

outerJoin :: Eq a => (a -> b -> Maybe c -> d) -> [(a, b)] -> [(a, c)] -> [d]
outerJoin f = outerJoinBy fst fst (\x y -> f (fst x) (snd x) (fmap snd y))

innerJoinBy :: Eq key => (a -> key) -> (b -> key) -> (a -> b -> c) -> [a] -> [b] -> [c]
innerJoinBy xsKey ysKey f xs ys =
  let joined = outerJoinBy xsKey ysKey (,) xs ys in [ f x y | (x, Just y) <- joined ]

innerJoin :: Eq a => (a -> b -> c -> d) -> [(a, b)] -> [(a, c)] -> [d]
innerJoin f = innerJoinBy fst fst (\x y -> f (fst x) (snd x) (snd y))
