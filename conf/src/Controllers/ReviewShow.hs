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

data ReviewData = ReviewData { reviewDataScore :: Int, reviewDataContent :: Text}

instance TemplateData ReviewData where
  templateFile = "review.show.html.mustache"

instance ToMustache ReviewData where
  toMustache (ReviewData score content) =
    Mustache.object ["score" ~> toMustache score, "content" ~> toMustache content]

-- If I inline these functions LH goes crazy
updateContent :: ReviewId -> Text -> Controller ()
updateContent id content = update id (reviewContent' `assign` content)
updateScore :: ReviewId -> Int -> Controller ()
updateScore id score = update id (reviewScore' `assign` score)

updateReview :: ReviewId -> Controller ()
updateReview reviewId = do
  viewer <- requireAuthUser
  isPC   <- pc viewer

  if not isPC || currentStage /= ReviewStage then respondTagged forbidden else return ()

  params <- parseForm
  case lookup "content" params of
    Just content -> updateContent reviewId (decodeUtf8 content)
    Nothing      -> return ()

  case lookup "score" params of
    Just score -> updateScore reviewId (read . show . decodeUtf8 $ score)
    Nothing    -> return ()

{-@ reviewShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
reviewShow :: Int64 -> Controller ()
reviewShow rid = do
  let reviewId = toSqlKey rid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer

  req      <- request
  if reqMethod req == methodPost then updateReview reviewId else return ()

  maybeReview <- selectFirst (reviewId' ==. reviewId)
  review      <- case maybeReview of
    Just review -> return review
    Nothing     -> respondTagged notFound

  isPC <- pc viewer
  case (isPC, currentStage) of
    (True, _) -> do
      reviewData <- project2 (reviewScore', reviewContent') review
      respondHtml (uncurry ReviewData reviewData)
    (_, PublicStage) -> do
      paperId <- project reviewPaper' review
      paper   <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. viewerId)
      case paper of
        Just _ -> do
          reviewData <- project2 (reviewScore', reviewContent') review
          respondHtml (uncurry ReviewData reviewData)
        Nothing -> return ()
    _ -> return ()

  respondTagged forbidden


