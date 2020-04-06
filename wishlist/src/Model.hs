{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Model where

import           Database.Persist               ( Key )
import           Database.Persist.TH            ( share
                                                , mkMigrate
                                                , mkPersist
                                                , sqlSettings
                                                , persistLowerCase
                                                )
import           Data.Text                      ( Text )
import qualified Database.Persist              as Persist

import           Binah.Core

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  name Text
  username Text

Wish
  owner UserId
  description Text
  accessLevel String

Friendship
  user1 UserId
  user2 UserId
|]

{-@
data EntityFieldWrapper record typ < policy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   > = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

{-@ measure friends :: UserId -> UserId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

{-@ predicate PublicOrFriends WISH VIEWER = wishAccessLevel (entityVal WISH) == "public" || wishOwner (entityVal WISH) == entityKey VIEWER || (wishAccessLevel (entityVal WISH) == "friends" && friends (wishOwner (entityVal WISH)) (entityKey VIEWER)) @-}

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

-- * User

{-@ data User = User
  { userName :: _
  , userUsername :: _
  }
@-}

{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ assume userName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userUsername' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userUsername (entityVal row)}
  , {\field row  -> field == userUsername (entityVal row)}
  > _ _
@-}
userUsername' :: EntityFieldWrapper User Text
userUsername' = EntityFieldWrapper UserUsername

-- * Wish

{-@ data Wish = Wish
  { wishOwner :: _
  , wishDescription :: _
  , wishAccessLevel :: _
  }
@-}

{-@ assume wishId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
wishId' :: EntityFieldWrapper Wish WishId
wishId' = EntityFieldWrapper WishId

{-@ assume wishOwner' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == wishOwner (entityVal row)}
  , {\field row  -> field == wishOwner (entityVal row)}
  > _ _
@-}
wishOwner' :: EntityFieldWrapper Wish UserId
wishOwner' = EntityFieldWrapper WishOwner

{-@ assume wishDescription' :: EntityFieldWrapper <
    {\row viewer -> PublicOrFriends row viewer}
  , {\row field  -> field == wishDescription (entityVal row)}
  , {\field row  -> field == wishDescription (entityVal row)}
  > _ _
@-}
wishDescription' :: EntityFieldWrapper Wish Text
wishDescription' = EntityFieldWrapper WishDescription

{-@ assume wishAccessLevel' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == wishAccessLevel (entityVal row)}
  , {\field row  -> field == wishAccessLevel (entityVal row)}
  > _ _
@-}
wishAccessLevel' :: EntityFieldWrapper Wish String
wishAccessLevel' = EntityFieldWrapper WishAccessLevel

-- * Friendship

{-@ data Friendship = Friendship
  { friendshipUser1 :: _
  , friendshipUser2 :: _
  }
@-}

{-@ invariant {v: Entity Friendship | friends (friendshipUser1 (entityVal v)) (friendshipUser2 (entityVal v))} @-}

{-@ assume friendshipId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
friendshipId' :: EntityFieldWrapper Friendship FriendshipId
friendshipId' = EntityFieldWrapper FriendshipId

{-@ assume friendshipUser1' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == friendshipUser1 (entityVal row)}
  , {\field row  -> field == friendshipUser1 (entityVal row)}
  > _ _
@-}
friendshipUser1' :: EntityFieldWrapper Friendship UserId
friendshipUser1' = EntityFieldWrapper FriendshipUser1

{-@ assume friendshipUser2' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == friendshipUser2 (entityVal row)}
  , {\field row  -> field == friendshipUser2 (entityVal row)}
  > _ _
@-}
friendshipUser2' :: EntityFieldWrapper Friendship UserId
friendshipUser2' = EntityFieldWrapper FriendshipUser2
