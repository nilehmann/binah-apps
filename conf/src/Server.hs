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
import qualified Database.Persist              as Persistent

import           Binah.Frankie
import           Binah.Infrastructure
import           Binah.Insert

import           Controllers
import           Controllers.Paper
import           Controllers.Home
import           Model
import           Data.Pool                      ( Pool )
import qualified Data.Pool                     as Pool
import           Text.Mustache.Compile          ( TemplateCache )
import           Control.Monad.Base             ( MonadBase(..) )
import           Control.Monad.Trans.Control    ( MonadBaseControl(..)
                                                , MonadTransControl(..)
                                                , RunInBase
                                                )
import           Control.Monad.Trans.Class      ( lift )
import           Control.Monad.Logger           ( runNoLoggingT )



runServer :: IO ()
runServer = runNoLoggingT $ do
    pool  <- createSqlitePool "db.sqlite" 1

    cache <- liftIO $ MVar.newMVar mempty

    liftIO . runFrankieServer "dev" $ do
        mode "dev" $ do
            host "localhost"
            port 3000
            initWith $ initFromPool cache pool
        dispatch $ do
            get "/"      homeAuthor
            get "/paper" paperNew
            post "/paper" paperNew
            get "/paper/:pid"      paperShow
            get "/paper/:pid/edit" paperEdit
            post "/paper/:pid/edit" paperEdit

            get "/chair" homeChair

            fallback $ respond notFound


initDB :: IO ()
initDB = runSqlite "db.sqlite" $ do
    runMigration migrateAll
    Persistent.insert (User "nadia" "Nadia Polikarpova" "npolikarpova@ucsd.edu" "ucsd" "chair")
    Persistent.insert (User "ranjit" "Ranjit Jhala" "npolikarpova@ucsd.edu" "ucsd" "pc")
    Persistent.insert (User "rose" "Rose Kunkel" "rkunkel@ucsd.edu" "ucsd" "author")

    return ()

-- TODO find a way to provide this without exposing the instance of MonadBaseControl

initFromPool :: MVar.MVar TemplateCache -> Pool SqlBackend -> Controller () -> ControllerT TIO ()
initFromPool cache pool controller = Pool.withResource pool $ \sqlBackend ->
    configure (Config sqlBackend cache httpAuthDb) . reading backend . unTag $ controller

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
