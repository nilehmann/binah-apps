{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Server
    ( runServer
    , initDB
    )
where

import qualified Control.Concurrent.MVar       as MVar
import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , ReaderT(..)
                                                )
import           Database.Persist.Sqlite        ( SqlBackend
                                                , runSqlite
                                                , runMigration
                                                , createSqlitePool
                                                )
import           Frankie.Config
import           Frankie.Auth

import           Data.Pool                      ( Pool )
import qualified Data.Pool                     as Pool
import           Control.Monad.Base             ( MonadBase(..) )
import           Control.Monad.Trans.Control    ( MonadBaseControl(..)
                                                , MonadTransControl(..)
                                                )
import           Control.Monad.Trans.Class      ( lift )
import           Control.Monad.Logger           ( runNoLoggingT )

import           Binah.Core
import           Binah.Frankie
import           Binah.Infrastructure
import           Binah.Insert
import           Binah.Actions
import           Binah.Filters

import           Controllers
import           Model
import           Auth



{-@ ignore runServer @-}
runServer :: IO ()
runServer = runNoLoggingT $ do
    pool <- createSqlitePool "db.sqlite" 1
    liftIO . runFrankieServer "dev" $ do
        mode "dev" $ do
            host "localhost"
            port 3000
            initWith $ initFromPool pool
        dispatch $ do
            post "/sign_in" signIn
            fallback $ respond404 Nothing

{-@ ignore httpAuthDb @-}
httpAuthDb :: AuthMethod (Entity User) Controller
httpAuthDb = httpBasicAuth $ \username _password -> selectFirst (userUsername' ==. username)


{-@ ignore initDB @-}
initDB :: IO ()
initDB = runSqlite "db.sqlite" $ do
    runMigration migrateAll

-- TODO find a way to provide this without exposing the instance of MonadBaseControl

initFromPool :: Pool SqlBackend -> Controller () -> ControllerT TIO ()
initFromPool pool controller = Pool.withResource pool $ \sqlBackend ->
    configure (Config sqlBackend httpAuthDb) . reading backend . unTag $ controller

instance MonadBase IO TIO where
    liftBase = TIO

instance MonadBaseControl IO TIO where
    type StM TIO a = a
    liftBaseWith f = TIO (f runTIO)
    restoreM = return

instance MonadBase IO (ControllerT TIO) where
    liftBase = lift . liftBase

instance MonadBaseControl IO (ControllerT TIO) where
    type StM (ControllerT TIO) a = ControllerStatus a
    liftBaseWith f = ControllerT $ \r -> TIO $ fmap Working (f (runTIO . flip runController r))
    restoreM st = ControllerT $ \_ -> return st
