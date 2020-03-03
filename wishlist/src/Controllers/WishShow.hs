{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.WishShow where

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


data WishData = WishData { wishDataDescription :: Text }

instance TemplateData WishData where
  templateFile = "wish.show.html.mustache"


instance ToMustache WishData where
  toMustache (WishData description) = Mustache.object ["description" ~> description]

{-@ wishShow :: WishId -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
wishShow :: WishId -> Controller ()
wishShow wishId = do
  viewer    <- requireAuthUser
  viewerId  <- project userId' viewer
  maybeWish <- selectFirst (wishId' ==. wishId)
  wish      <- case maybeWish of
    Just wish -> return wish
    Nothing   -> respondTagged notFound

  level   <- project wishAccessLevel' wish
  owner   <- project wishOwner' wish
  friends <- selectFirst (friendshipUser1' ==. owner &&: friendshipUser2' ==. viewerId)

  descr   <- case (owner == viewerId, friends) of
    (True, _)             -> project wishDescription' wish
    (_, Just _) | level == "friends" -> project wishDescription' wish
    _ | level == "public" -> project wishDescription' wish
    _                     -> respondTagged forbidden

  respondHtml $ WishData descr
