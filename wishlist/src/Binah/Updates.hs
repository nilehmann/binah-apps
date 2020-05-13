{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Binah.Updates
  ( assign
  , updateWhere
  )
where

import           Control.Monad.Reader
import           Database.Persist               ( PersistRecordBackend
                                                , PersistField
                                                )
import qualified Database.Persist              as Persist

import           Binah.Core
import           Binah.Filters
import           Binah.Infrastructure
import           Model

{-@ 
newtype Update record < visibility :: Entity record -> Entity User -> Bool
                      , update :: Entity record -> Bool
                      , capabilities :: Entity record -> Bool
                      , policy :: Entity record -> Entity record -> Entity User -> Bool
                      > = Update _ @-}
newtype Update record = Update [Persist.Update record]
{-@ data variance Update invariant invariant invariant @-}

-- For some reason the type is not exported if we use `=.`
{-@ ignore assign @-}
{-@
assume assign :: forall < policy :: Entity record -> Entity User -> Bool
                        , selector :: Entity record -> typ -> Bool
                        , flippedselector :: typ -> Entity record -> Bool
                        , r :: typ -> Bool
                        , update :: Entity record -> Bool
                        , fieldref :: typ -> Bool
                        , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                        , capability :: Entity record -> Bool
                        >.
  { row :: (Entity record)
  , value :: typ<r>
  , field :: {field:(typ<selector row>) | field == value}
      |- {v:(Entity <flippedselector field> record) | True} <: {v:(Entity <update> record) | True}
  }
  
  EntityFieldWrapper<policy, selector, flippedselector, capability, updatepolicy> record typ 
  -> typ<r> 
  -> Update<policy, update, capability, updatepolicy> record
@-}
assign :: PersistField typ => EntityFieldWrapper record typ -> typ -> Update record
assign (EntityFieldWrapper field) val = Update [field Persist.=. val]


-- TODO: It's probably important to make sure multiple updates to the same field don't happen at once
{-@
instance Semigroup (Update record) where
  assume (<>) :: forall < visibility1 :: Entity record -> Entity User -> Bool
                        , visibility2 :: Entity record -> Entity User -> Bool
                        , visibility  :: Entity record -> Entity User -> Bool
                        , update1 :: Entity record -> Bool
                        , update2 :: Entity record -> Bool
                        , update  :: Entity record -> Bool
                        , cap1 :: Entity record -> Bool
                        , cap2 :: Entity record -> Bool
                        , cap  :: Entity record -> Bool
                        , policy1 :: Entity record -> Entity record -> Entity User -> Bool
                        , policy2 :: Entity record -> Entity record -> Entity User -> Bool
                        , policy  :: Entity record -> Entity record -> Entity User -> Bool
                        >.
    { row :: (Entity<update> record) 
        |- {v:(Entity<visibility1 row> User) | True} <: {v:(Entity<visibility row>) | True} 
    }
    { row :: (Entity<update> record) 
        |- {v:(Entity<visibility2 row> User) | True} <: {v:(Entity<visibility row>) | True} 
    }

    { {v: (Entity<update> record) | True } <: {v: (Entity<update1> record) | True}}
    { {v: (Entity<update> record) | True } <: {v: (Entity<update2> record) | True}}
    { row1 :: (Entity<update1> record)
    , row2 :: (Entity<update2> record) 
        |- {v:(Entity record) | v == row1 && v == row2} <: {v:(Entity<update> record) | True} 
    }

    { {v: (Entity<cap> record) | True } <: {v: (Entity<cap1> record) | True}}
    { {v: (Entity<cap> record) | True } <: {v: (Entity<cap2> record) | True}}
    { row1 :: (Entity<cap1> record)
    , row2 :: (Entity<cap2> record) 
        |- {v:(Entity record) | v == row1 && v == row2} <: {v:(Entity<cap> record) | True} 
    }

    { old :: Entity record
    , new :: Entity record
       |- {v: (Entity<policy old new> User) | True } <: {v: (Entity<policy1 old new> User) | True}
    }
    { old :: Entity record
    , new :: Entity record
       |- {v: (Entity<policy old new> User) | True } <: {v: (Entity<policy2 old new> User) | True}
    }
    { old :: Entity record
    , new :: Entity record
    , row1 :: (Entity<policy1 old new> User)
    , row2 :: (Entity<policy2 old new> User) 
        |- {v:(Entity User) | v == row1 && v == row2} <: {v:(Entity<policy old new> User) | True} 
    }

    Update<visibility1, update1, cap1, policy1> 
    -> Update<visibility2, update2, cap2, policy2> 
    -> Update<visibility, update, cap, policy>
@-}
instance Semigroup (Update record) where
  (<>) = combineUpdates

-- TODO: Why does this make liquid crash w/out ignore
{-@ ignore combineUpdates @-}
combineUpdates :: Update record -> Update record -> Update record
combineUpdates (Update us1) (Update us2) = Update (us1 ++ us2)


-- TODO: Figure out what to do with the key
{-@ ignore updateWhere @-}
{-@
assume updateWhere :: forall < visibility :: Entity record -> Entity User -> Bool
                             , update :: Entity record -> Bool
                             , audience :: Entity User -> Bool
                             , capabilities :: Entity record -> Bool
                             , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                             , querypolicy :: Entity record -> Entity User -> Bool
                             , filter :: Entity record -> Bool
                             >.
  { row :: (Entity<update> record) 
      |- {v:(Entity<visibility row> User) | True} <: {v:(Entity<audience> User) | True} 
  }

  { old  :: (Entity<filter> record)
  , new  :: (Entity<update> record)
  , user :: {v: (Entity<updatepolicy old new> User) | v == currentUser}
      |- {v:(Entity record) | True} <: {v:(Entity<capabilities> record) | True}
  }

  Filter<querypolicy, filter> record
  -> Update<visibility, update, capabilities, updatepolicy> record 
  -> TaggedT<{\_ -> True}, audience> m ()
@-}
updateWhere
  :: ( MonadTIO m
     , Persist.PersistQueryWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => Filter record
  -> Update record
  -> TaggedT m ()
updateWhere (Filter filters) (Update up) = do
  backend <- ask
  liftTIO (TIO $ runReaderT (Persist.updateWhere filters up) backend)
