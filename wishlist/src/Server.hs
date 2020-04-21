{-# LANGUAGE OverloadedStrings #-}
module Server
    ( runServer
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
                                                )
import           Frankie.Config
import qualified Database.Persist              as Persistent

import           Binah.Frankie
import           Binah.Infrastructure
import           Binah.Insert

import           Controllers
import           Controllers.Wish               ( wishNew
                                                , wishShow
                                                , wishEdit
                                                )
import           Controllers.User               ( userShow )
import           Model


setup :: MonadIO m => ReaderT SqlBackend m Config
setup = do
    templateCache <- liftIO $ MVar.newMVar mempty
    runMigration migrateAll

    Persistent.insert (User "Nico" "nico")

    backend <- ask
    return $ Config { configBackend       = backend
                    , configTemplateCache = templateCache
                    , configAuthMethod    = httpAuthDb
                    }


runServer :: IO ()
runServer = runSqlite "db.sqlite" $ do
    cfg <- setup
    liftIO . runFrankieServer "dev" $ do
        mode "dev" $ do
            host "localhost"
            port 3000
            initWith $ configure cfg . reading backend . unTag
        dispatch $ do
            get "/user/:uid" userShow
            get "/wish"      wishNew
            post "/wish" wishNew
            get "/wish/:wid"      wishShow
            get "/wish/:wid/edit" wishEdit
            post "/wish/:wid/edit" wishEdit
            fallback $ respond notFound
