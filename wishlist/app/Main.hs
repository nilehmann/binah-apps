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

import           Controllers.WishShow
import           Controllers.WishIndex

main :: IO ()
main = undefined
