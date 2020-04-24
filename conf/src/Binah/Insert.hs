{-# LANGUAGE GADTs #-}
module Binah.Insert where


import           Binah.Infrastructure
import           Control.Monad.Reader           ( MonadReader(..)
                                                , runReaderT
                                                )
import qualified Database.Persist              as Persist

import           Model


{-@ ignore insert @-}
insert
    :: ( MonadTIO m
       , Persist.PersistStoreWrite backend
       , Persist.PersistRecordBackend record backend
       , MonadReader backend m
       )
    => record
    -> TaggedT m (Persist.Key record)
insert record = do
    backend <- ask
    liftTIO . TIO $ runReaderT (Persist.insert record) backend

