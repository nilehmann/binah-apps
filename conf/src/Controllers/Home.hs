{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.Home where

-- I get a liquid haskell error if I don't import this
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache

import           Binah.Core
import           Binah.Actions
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Binah.Helpers
import           Binah.Filters
import           Model

import           Controllers
import           Database.Persist.Sql           ( fromSqlKey )

data HomeAuthor = HomeAuthor [PaperData]

instance ToMustache HomeAuthor where
  toMustache (HomeAuthor papers) = Mustache.object ["papers" ~> papers]


instance ToMustache PaperData where
  toMustache (PaperData paperId paperTitle) =
    Mustache.object ["paperId" ~> paperId, "title" ~> paperTitle]

data PaperData = PaperData
  { paperDataId :: PaperId
  , paperDataTitle :: Text
  }

{-@ homeAuthor :: TaggedT<{\_ -> False}, {\_ -> True}> _ _@-}
homeAuthor :: Controller ()
homeAuthor = do
  viewer    <- requireAuthUser
  viewerId  <- project userId' viewer
  papers    <- selectList (paperAuthor' ==. viewerId)
  paperData <- projectList2 (paperId', paperTitle') papers
  respondHtml "home.html.mustache" (HomeAuthor (map (uncurry PaperData) paperData))
