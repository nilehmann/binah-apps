{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--compile-spec" @-}

module Model
  ( EntityFieldWrapper(..)
  , migrateAll
  , BinahRecord
  , persistentRecord
  , mkUser
  , mkWish
  , mkFriendship
  , User
  , Wish
  , Friendship
  , userId'
  , userName'
  , userUsername'
  , wishId'
  , wishOwner'
  , wishDescription'
  , wishAccessLevel'
  , friendshipId'
  , friendshipUser1'
  , friendshipUser2'
  , UserId
  , WishId
  , FriendshipId
  )
where

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
data EntityFieldWrapper record typ < querypolicy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   , capability :: Entity record -> Bool
                                   , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                                   > = EntityFieldWrapper _
@-}

data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

{-@ measure currentUser :: Entity User @-}

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

{-@ measure friends :: UserId -> UserId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

{-@ predicate PublicOrFriends WISH VIEWER = wishAccessLevel (entityVal WISH) == "public" || wishOwner (entityVal WISH) == entityKey VIEWER || (wishAccessLevel (entityVal WISH) == "friends" && friends (wishOwner (entityVal WISH)) (entityKey VIEWER)) @-}

{-@ predicate IsOwner WISH VIEWER = wishOwner (entityVal WISH) == entityKey VIEWER @-}

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ data BinahRecord record < 
    p :: Entity record -> Bool
  , insertpolicy :: Entity record -> Entity User -> Bool
  , querypolicy  :: Entity record -> Entity User -> Bool 
  >
  = BinahRecord _
@-}
data BinahRecord record = BinahRecord record
{-@ data variance BinahRecord invariant invariant invariant invariant @-}

{-@ persistentRecord :: BinahRecord record -> record @-}
persistentRecord :: BinahRecord record -> record
persistentRecord (BinahRecord record) = record

{-@ measure getJust :: Key record -> Entity record @-}

-- * User

{-@ measure userName :: User -> Text @-}
{-@ measure userUsername :: User -> Text @-}

{-@ mkUser :: 
     x_0: Text
  -> x_1: Text
  -> BinahRecord < 
       {\row -> userName (entityVal row) == x_0 && userUsername (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> False}
     > User
@-}
mkUser x_0 x_1 = BinahRecord (User x_0 x_1)

{-@ invariant {v: Entity User | v == getJust (entityKey v)} @-}



{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ measure userNameCap :: Entity User -> Bool @-}

{-@ assume userName' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  , {\row -> userNameCap row}
  , {\row _ _ -> userNameCap row}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ measure userUsernameCap :: Entity User -> Bool @-}

{-@ assume userUsername' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userUsername (entityVal row)}
  , {\field row  -> field == userUsername (entityVal row)}
  , {\row -> userUsernameCap row}
  , {\row _ _ -> userUsernameCap row}
  > _ _
@-}
userUsername' :: EntityFieldWrapper User Text
userUsername' = EntityFieldWrapper UserUsername

-- * Wish

{-@ measure wishOwner :: Wish -> UserId @-}
{-@ measure wishDescription :: Wish -> Text @-}
{-@ measure wishAccessLevel :: Wish -> String @-}

{-@ mkWish :: 
     x_0: UserId
  -> x_1: Text
  -> x_2: String
  -> BinahRecord < 
       {\row -> wishOwner (entityVal row) == x_0 && wishDescription (entityVal row) == x_1 && wishAccessLevel (entityVal row) == x_2}
     , {\wish viewer -> wishOwner (entityVal wish) == entityKey viewer}
     , {\row viewer -> (wishAccessLevel (entityVal row) == "public" || wishOwner (entityVal row) == entityKey viewer || (wishAccessLevel (entityVal row) == "friends" && friends (wishOwner (entityVal row)) (entityKey viewer)))}
     > Wish
@-}
mkWish x_0 x_1 x_2 = BinahRecord (Wish x_0 x_1 x_2)

{-@ invariant {v: Entity Wish | v == getJust (entityKey v)} @-}



{-@ assume wishId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
wishId' :: EntityFieldWrapper Wish WishId
wishId' = EntityFieldWrapper WishId

{-@ measure wishOwnerCap :: Entity Wish -> Bool @-}

{-@ assume wishOwner' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == wishOwner (entityVal row)}
  , {\field row  -> field == wishOwner (entityVal row)}
  , {\old -> wishOwnerCap old}
  , {\old new user -> entityKey user == wishOwner (entityVal old) => wishOwnerCap old}
  > _ _
@-}
wishOwner' :: EntityFieldWrapper Wish UserId
wishOwner' = EntityFieldWrapper WishOwner

{-@ measure wishDescriptionCap :: Entity Wish -> Bool @-}

{-@ assume wishDescription' :: EntityFieldWrapper <
    {\wish viewer -> wishAccessLevel (entityVal wish) == "public" || wishOwner (entityVal wish) == entityKey viewer || (wishAccessLevel (entityVal wish) == "friends" && friends (wishOwner (entityVal wish)) (entityKey viewer))}
  , {\row field  -> field == wishDescription (entityVal row)}
  , {\field row  -> field == wishDescription (entityVal row)}
  , {\row -> wishDescriptionCap row}
  , {\row _ _ -> wishDescriptionCap row}
  > _ _
@-}
wishDescription' :: EntityFieldWrapper Wish Text
wishDescription' = EntityFieldWrapper WishDescription

{-@ measure wishAccessLevelCap :: Entity Wish -> Bool @-}

{-@ assume wishAccessLevel' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == wishAccessLevel (entityVal row)}
  , {\field row  -> field == wishAccessLevel (entityVal row)}
  , {\row -> wishAccessLevelCap row}
  , {\row _ _ -> wishAccessLevelCap row}
  > _ _
@-}
wishAccessLevel' :: EntityFieldWrapper Wish String
wishAccessLevel' = EntityFieldWrapper WishAccessLevel

-- * Friendship

{-@ measure friendshipUser1 :: Friendship -> UserId @-}
{-@ measure friendshipUser2 :: Friendship -> UserId @-}

{-@ mkFriendship :: 
     x_0: UserId
  -> x_1: UserId
  -> BinahRecord < 
       {\row -> friendshipUser1 (entityVal row) == x_0 && friendshipUser2 (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> False}
     > Friendship
@-}
mkFriendship x_0 x_1 = BinahRecord (Friendship x_0 x_1)

{-@ invariant {v: Entity Friendship | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity Friendship | friends (friendshipUser1 (entityVal v)) (friendshipUser2 (entityVal v))} @-}

{-@ assume friendshipId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
friendshipId' :: EntityFieldWrapper Friendship FriendshipId
friendshipId' = EntityFieldWrapper FriendshipId

{-@ measure friendshipUser1Cap :: Entity Friendship -> Bool @-}

{-@ assume friendshipUser1' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == friendshipUser1 (entityVal row)}
  , {\field row  -> field == friendshipUser1 (entityVal row)}
  , {\row -> friendshipUser1Cap row}
  , {\row _ _ -> friendshipUser1Cap row}
  > _ _
@-}
friendshipUser1' :: EntityFieldWrapper Friendship UserId
friendshipUser1' = EntityFieldWrapper FriendshipUser1

{-@ measure friendshipUser2Cap :: Entity Friendship -> Bool @-}

{-@ assume friendshipUser2' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == friendshipUser2 (entityVal row)}
  , {\field row  -> field == friendshipUser2 (entityVal row)}
  , {\row -> friendshipUser2Cap row}
  , {\row _ _ -> friendshipUser2Cap row}
  > _ _
@-}
friendshipUser2' :: EntityFieldWrapper Friendship UserId
friendshipUser2' = EntityFieldWrapper FriendshipUser2

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------


