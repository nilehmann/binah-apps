{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Control.Concurrent.MVar       as MVar
import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , ReaderT(..)
                                                )

import           Data.Text                      ( Text )
import qualified Database.Persist.Sqlite       as Sqlite
import qualified Database.Persist              as Persist
import           Frankie
import           Frankie.Config

import           Binah.Filters
import           Binah.Updates
import           Binah.Infrastructure
import           Binah.Frankie
import           Controllers
import           Model

import           Controllers.Home
import           Controllers.PaperShow
import           Controllers.PaperIndex
import           Controllers.ReviewShow
import           Controllers.ProfileShow


jeevesAbstract :: Text
jeevesAbstract =
  "It is important for applications to protect sensitive data. Even forsimple confidentiality and integrity policies, it is often difficult forprogrammers to reason about how the policies should interact andhow to enforce policies across the program. A promising approach is policy-agnostic programming, a model that allows the program-mer to implement policies separately from core functionality. Yanget al. describe Jeeves [48], a programming language that supportsinformation flow policies describing how to reveal sensitive val-ues in different output channels. Jeeves uses symbolic evaluationand constraint-solving to produce outputs adhering to the policies.This strategy provides strong confidentiality guarantees but limitsexpressiveness and implementation feasibility.We extend Jeeves withfaceted values[6], which exploit thestructure of sensitive values to yield both greater expressiveness andto facilitate reasoning about runtime behavior. We presenta facetedsemantics for Jeeves and describe a model for propagating multipleviews of sensitive information through a program. We provide a proof of termination-insensitive non-interference and describe howthe semantics facilitate reasoning about program behavior."

setup :: MonadIO m => ReaderT Sqlite.SqlBackend m Config
setup = do
  templateCache <- liftIO $ MVar.newMVar mempty

  Sqlite.runMigration migrateAll

  nadiaId <- Persist.insert
    $ User "nadia" "Nadia Polikarpova" "npolikarpova@eng.ucsd.edu" "UC San Diego" "chair"
  nicoId <- Persist.insert $ User "nico" "Nico Lehmann" "nlehmann@eng.ucsd.edu" "UC San Diego" "pc"
  matiasId <- Persist.insert
    $ User "matias" "Matias Toro" "mtoro@dcc.uchile.cl" "University of Chile" "normal"

  thomasId <- Persist.insert
    $ User "thomas" "Thomas H. Austin" "taustin@ucsc.edu" "UC Santa Cruz" "normal"

  jeevesId <- Persist.insert
    $ Paper thomasId "Faceted Execution of Policy-Agnostic Programs" jeevesAbstract False
  Persist.insert $ PaperCoauthor jeevesId "Jean Yang"
  Persist.insert $ PaperCoauthor jeevesId "Cormac Flanagan"

  backend <- ask

  return $ Config { configBackend       = backend
                  , configTemplateCache = templateCache
                  , configAuthMethod    = httpAuthDb
                  }


{-@ ignore main @-}
main :: IO ()
main = Sqlite.runSqlite ":memory:" $ do
  cfg <- setup
  liftIO . runFrankieServer "dev" $ do
    mode "dev" $ do
      host "localhost"
      port 3000
      initWith $ configure cfg . reading backend . unTag
    dispatch $ do
      get "/"              home
      get "/papers"        paperIndex
      get "/papers/:pid"   paperShow
      get "/profiles/:uid" profileShow
      fallback $ respond notFound



