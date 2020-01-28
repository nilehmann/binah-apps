{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Main where

import           Database.Persist.Sql           ( toSqlKey )
import           Control.Monad.Reader           ( ReaderT(..) )
import           Database.Persist.Sqlite        ( SqlBackend )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import qualified Control.Concurrent.MVar       as MVar
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Frankie
import           Frankie.Auth
import           Frankie.Config
import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Model

type T = TaggedT (ReaderT SqlBackend TIO)

main :: IO ()
main = undefined

{-@ showWishes :: Entity User -> UserId -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
showWishes :: Entity User -> UserId -> T ()
showWishes viewer userId = do
  viewerId     <- project userId' viewer
  friends      <- selectFirst (friendsUser1' ==. userId &&: friendsUser2' ==. viewerId)
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
  printTo viewer (show descriptions)

{-@ notifyFriends :: UserId -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
notifyFriends :: UserId -> T ()
notifyFriends birthdayUserId = do
  -- Get list of friends
  friendships <- selectList (friendsUser1' ==. birthdayUserId)
  friendsIds <- projectList friendsUser2' friendships
  friends <- selectList (userId' <-. friendsIds)
  -- Get list of wishes
  wishes <- selectList (wishOwner' ==. birthdayUserId &&: wishAccessLevel' ==. "friends")
  descriptions <- projectList wishDescription' wishes
  -- Send emails to all friends
  printAll friends (show descriptions)
