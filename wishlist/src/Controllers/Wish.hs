{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.Wish where

import           Database.Persist.Sql           ( toSqlKey
                                                , fromSqlKey
                                                )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Text.Encoding             ( decodeUtf8
                                                , encodeUtf8
                                                )
import           Data.Function                  ( (&) )
import           Data.Maybe                     ( fromMaybe )
import           Data.ByteString                ( ByteString )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as M
import           Text.Printf                    ( printf )
import           Frankie

import           Binah.Core
import           Binah.Actions
import           Binah.Updates
import           Binah.Insert
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Model

import           Helpers
import           Controllers
import           Control.Monad                  ( when )

newtype WishNew = WishNew String
data WishEdit = WishEdit String WishData
data WishData = WishData Text String

instance ToMustache WishData where
  toMustache (WishData descr level) = M.object ["description" ~> descr, "accessLevel" ~> level]

instance ToMustache WishNew where
  toMustache (WishNew action) = M.object
    ["action" ~> action, "accessLevels" ~> map (uncurry (getAccessLevel False)) accessLevels]

instance ToMustache WishEdit where
  toMustache (WishEdit action (WishData descr level)) = M.object
    [ "action" ~> action
    , "description" ~> descr
    , "accessLevels"
      ~> [ getAccessLevel (value == level) value label | (value, label) <- accessLevels ]
    ]

accessLevels :: [(String, String)]
accessLevels = [("private", "Private"), ("public", "Public"), ("friends", "Friends")]

getAccessLevel :: Bool -> String -> String -> M.Value
getAccessLevel isSelected value label = M.object
  ["value" ~> value, "label" ~> label, "selected" ~> (selected :: String)]
  where selected = if isSelected then "selected" else ""

-----------------------------------------------------------------------------------
-- | New Wish
-----------------------------------------------------------------------------------

{-@ wishNew :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
wishNew :: Controller ()
wishNew = do
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  req      <- request
  if reqMethod req == methodPost
    then insertWish viewerId
    else respondHtml "wish.edit.html.mustache" (WishNew "/wish")


{-@ insertWish :: {v: UserId | v == entityKey currentUser} -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
insertWish :: UserId -> Controller ()
insertWish userId = do
  params <- parseForm
  let descr       = lookup "description" params
  let accessLevel = lookup "accessLevel" params & fmap Text.unpack
  case (descr, accessLevel) of
    (Just descr, Just accessLevel) -> do
      -- ENFORCE: userId == viewerId
      wishId <- insert (mkWish userId descr accessLevel)
      respondTagged (redirectTo (wishRoute wishId))
    _ -> respondTagged badRequest

-----------------------------------------------------------------------------------
-- | Edit Wish
-----------------------------------------------------------------------------------

{-@ wishEdit :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
wishEdit :: Int64 -> Controller ()
wishEdit wid = do
  let wishId = toSqlKey wid
  req <- request
  when (reqMethod req == methodPost) (updateWish wishId)
  wishData <- getWishData wishId
  respondHtml "wish.edit.html.mustache" (WishEdit (wishEditRoute wishId) wishData)


{-@ updateWish :: _ -> TaggedT<{\_ -> True}, {\_ -> True}> _ _ @-}
updateWish :: WishId -> Controller ()
updateWish id = do
  params <- parseForm
  case lookup "description" params of
    -- ENFORCE: User is the owner of the wish
    Just content -> updateWhere (wishId' ==. id) (wishDescription' `assign` content)
    Nothing      -> return ()

  case lookup "accessLevel" params of
    -- ENFORCE: User is the owner of the wish
    Just accessLevel ->
      updateWhere (wishId' ==. id) (wishAccessLevel' `assign` Text.unpack accessLevel)
    Nothing -> return ()

-----------------------------------------------------------------------------------
-- | Show Wish
-----------------------------------------------------------------------------------

{-@ wishShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
wishShow :: Int64 -> Controller ()
wishShow wid = do
  let wishId = toSqlKey wid
  wishData <- getWishData wishId
  respondHtml "wish.show.html.mustache" wishData

-----------------------------------------------------------------------------------
-- | Misc
-----------------------------------------------------------------------------------

{-@ getWishData :: _ -> TaggedT<{\v -> currentUser == v}, {\v -> True}> _ _ @-}
getWishData :: WishId -> Controller WishData
getWishData wishId = do
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  wish     <- selectFirstOr404 (wishId' ==. wishId)

  level    <- project wishAccessLevel' wish
  owner    <- project wishOwner' wish
  friends  <- selectFirst (friendshipUser1' ==. owner &&: friendshipUser2' ==. viewerId)

  descr    <- case (owner == viewerId, friends) of
    (True, _)             -> project wishDescription' wish
    (_, Just _) | level == "friends" -> project wishDescription' wish
    _ | level == "public" -> project wishDescription' wish
    _                     -> respondTagged forbidden

  return (WishData descr level)


wishRoute :: WishId -> ByteString
wishRoute wishId = encodeUtf8 (Text.pack path)
 where
  wid  = fromSqlKey wishId
  path = printf "/wish/%d" wid


wishEditRoute :: WishId -> String
wishEditRoute wishId = printf "/wish/%d/edit" wid where wid = fromSqlKey wishId

