{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.WishIndex where

import           Database.Persist.Sql           ( toSqlKey )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Frankie

import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Model

import           Helpers
import           Controllers


data WishIndex = WishIndex [WishData]

instance TemplateData WishIndex where
  templateFile = "wish.index.html.mustache"

instance ToMustache WishIndex where
  toMustache (WishIndex wishes) = Mustache.object ["wishes" ~> map toMustache wishes]

data WishData = WishData { wishDataDescription :: Text }

instance ToMustache WishData where
  toMustache (WishData description) = Mustache.object ["description" ~> description]

{-@ wishIndex :: UserId -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
wishIndex :: UserId -> Controller ()
wishIndex userId = do
  viewer       <- requireAuthUser
  viewerId     <- project userId' viewer
  friends      <- selectFirst (friendshipUser1' ==. userId &&: friendshipUser2' ==. viewerId)
  descriptions <- case (viewerId == userId, friends) of
    (True, _) -> do
      wishes <- selectList (wishOwner' ==. userId)
      projectList wishDescription' wishes
    (_, Just _) -> do
      wishes <- selectList (wishOwner' ==. userId &&: wishAccessLevel' <-. ["friends", "public"])
      projectList wishDescription' wishes
    _ -> do
      wishes <- selectList (wishOwner' ==. userId &&: wishAccessLevel' ==. "public")
      projectList wishDescription' wishes
  respondHtml $ WishIndex (map WishData descriptions)
