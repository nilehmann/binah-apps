{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.ReviewShow where

import           Database.Persist.Sql           ( toSqlKey )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import           Data.Text.Encoding             ( decodeUtf8 )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Frankie

import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Binah.Updates
import           Model

import           Helpers
import           Controllers
import           Control.Monad                  ( when )

data ReviewData = ReviewData { reviewDataScore :: Int, reviewDataContent :: Text}

instance ToMustache ReviewData where
  toMustache (ReviewData score content) =
    Mustache.object ["score" ~> toMustache score, "content" ~> toMustache content]


updateReview :: ReviewId -> Controller ()
updateReview reviewId = do
  viewer <- requireAuthUser
  isPC   <- pc viewer

  when (not isPC || currentStage /= ReviewStage) (respondTagged forbidden)

  params <- parseForm
  case lookup "content" params of
    Just content -> update reviewId (reviewContent' `assign` content)
    Nothing      -> return ()

  case lookup "score" params of
    Just score -> update reviewId (reviewScore' `assign` read (show score))
    Nothing    -> return ()

{-@ reviewShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
reviewShow :: Int64 -> Controller ()
reviewShow rid = do
  let reviewId = toSqlKey rid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer

  req      <- request

  when (reqMethod req == methodPost) (updateReview reviewId)

  maybeReview <- selectFirst (reviewId' ==. reviewId)
  review      <- case maybeReview of
    Just review -> return review
    Nothing     -> respondTagged notFound

  isPC <- pc viewer
  case (isPC, currentStage) of
    (True, _) -> do
      reviewData <- project2 (reviewScore', reviewContent') review
      respondHtml "review.show.html.mustache" (uncurry ReviewData reviewData)
    (_, PublicStage) -> do
      paperId <- project reviewPaper' review
      paper   <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. viewerId)
      case paper of
        Just _ -> do
          reviewData <- project2 (reviewScore', reviewContent') review
          respondHtml "review.show.html.mustache" (uncurry ReviewData reviewData)
        Nothing -> return ()
    _ -> return ()

  respondTagged forbidden


