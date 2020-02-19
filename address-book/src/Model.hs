{-
predicate friends :: UserId -> UserId -> Bool

User
  username Text
  name Text     {\viewer -> userVerified viewer || (entityKey viewer) == self}
  email Text    {\viewer -> userVerified viewer || (entityKey viewer) == self}
  address Text  {\viewer -> friends self (entityKey viewer) || (entityKey viewer) == self}
  verified Bool

FriendRequest
  from UserId   {\viewer -> (entityKey viewer) == from ||
                            (entityKey viewer) == to   ||
                            (accepted => (friends (entityKey viewer) from || friends (entityKey viewer) to))}
  to UserId     {\viewer -> (entityKey viewer) == from ||
                            (entityKey viewer) == to   ||
                            (accepted => (friends (entityKey viewer) from || friends (entityKey viewer) to))}
  accepted Bool {\viewer -> (entityKey viewer) == from ||
                            (entityKey viewer) == to   ||
                            (accepted => (friends (entityKey viewer) from || friends (entityKey viewer) to))}

  assert (accepted => friends from to)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
import Binah.Core

{-@
data EntityFieldWrapper record typ <policy :: Entity record -> Entity User -> Bool,
                                    selector :: Entity record -> typ -> Bool,
                                    flippedselector :: typ -> Entity record -> Bool> = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  username Text
  name Text
  email Text
  address Text
  verified Bool
  deriving Show

FriendRequest
  from UserId
  to UserId
  accepted Bool
  deriving Show
|]
-- * Predicate
{-@ measure friends :: UserId -> UserId -> Bool @-}

-- * User
{-@
data User = User
  { userUsername :: _
  , userName     :: _
  , userEmail    :: _
  , userAddress  :: _
  , userVerified :: _
  }
@-}

{-@ assume userIdField :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > User UserId @-}
userIdField :: EntityFieldWrapper User UserId
userIdField = EntityFieldWrapper UserId

{-@ assume userUsernameField :: EntityFieldWrapper <
    {\row viewer -> userVerified (entityVal viewer) || (entityKey viewer) == (entityKey row)}
  , {\row field -> field == userUsername (entityVal row)}
  , {\field row -> field == userUsername (entityVal row)}
  > User Text @-}
userUsernameField :: EntityFieldWrapper User Text
userUsernameField = EntityFieldWrapper UserUsername

{-@ assume userNameField :: EntityFieldWrapper <
    {\row viewer -> userVerified (entityVal viewer) || (entityKey viewer) == (entityKey row)}
  , {\row field -> field == userName (entityVal row)}
  , {\field row -> field == userName (entityVal row)}
  > User Text @-}
userNameField :: EntityFieldWrapper User Text
userNameField = EntityFieldWrapper UserName

{-@ assume userEmailField :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userEmail (entityVal row)}
  , {\field row -> field == userEmail (entityVal row)}
  > _ _ @-}
userEmailField :: EntityFieldWrapper User Text
userEmailField = EntityFieldWrapper UserEmail

{-@ assume userAddressField :: EntityFieldWrapper <
    {\row viewer -> friends (entityKey viewer) (entityKey row) || (entityKey viewer) == (entityKey row)}
  , {\row field -> field == userAddress (entityVal row)}
  , {\field row -> field == userAddress (entityVal row)}
  > User Text @-}
userAddressField :: EntityFieldWrapper User Text
userAddressField = EntityFieldWrapper UserAddress

{-@ assume userVerifiedField :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field = userVerified (entityVal row)}
  , {\field row -> field = userVerified (entityVal row)}
  > _ _ @-}
userVerifiedField :: EntityFieldWrapper User Bool
userVerifiedField = EntityFieldWrapper UserVerified

-- * FriendRequest

{-@
data FriendRequest = FriendRequest
  { friendRequestFrom :: Key User
  , friendRequestTo :: Key User
  , friendRequestAccepted :: Bool
  }
@-}

{-@ predicate IsEndpoint USER ROW = (entityKey USER) == friendRequestFrom (entityVal ROW) || (entityKey USER) == friendRequestTo (entityVal ROW)@-}
{-@ predicate IsFriendOfEndpoint VIEWER ROW = friends (entityKey VIEWER) (friendRequestFrom (entityVal ROW)) || friends (entityKey VIEWER) (friendRequestTo (entityVal ROW)) @-}

{-@ assume friendRequestFromField :: EntityFieldWrapper <
    {\row viewer -> (IsEndpoint viewer row) || (friendRequestAccepted (entityVal row) && IsFriendOfEndpoint viewer row)}
  , {\row field -> field = friendRequestFrom (entityVal row)}
  , {\field row -> field = friendRequestFrom (entityVal row)}
  > FriendRequest UserId @-}
friendRequestFromField :: EntityFieldWrapper FriendRequest (Key User)
friendRequestFromField = EntityFieldWrapper FriendRequestFrom

{-@ assume friendRequestToField :: EntityFieldWrapper <
    {\row viewer -> (IsEndpoint viewer row) || (friendRequestAccepted (entityVal row) && IsFriendOfEndpoint viewer row)}
  , {\row field -> field = friendRequestTo (entityVal row)}
  , {\field row -> field = friendRequestTo (entityVal row)}
  > FriendRequest UserId @-}
friendRequestToField :: EntityFieldWrapper FriendRequest (Key User)
friendRequestToField = EntityFieldWrapper FriendRequestTo

{-@ assume friendRequestAcceptedField :: EntityFieldWrapper <
    {\row viewer -> (IsEndpoint viewer row) || (friendRequestAccepted (entityVal row) && IsFriendOfEndpoint viewer row)}
  , {\row field -> field = friendRequestAccepted (entityVal row)}
  , {\field row -> field = friendRequestAccepted (entityVal row)}
  > FriendRequest Bool @-}
friendRequestAcceptedField :: EntityFieldWrapper FriendRequest Bool
friendRequestAcceptedField = EntityFieldWrapper FriendRequestAccepted

{-@ invariant {v:FriendRequest | friendRequestAccepted v => (friends (friendRequestFrom v) (friendRequestTo v) && friends (friendRequestTo v) (friendRequestFrom v))} @-}
