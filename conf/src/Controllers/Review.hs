{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.Review where

import           Database.Persist.Sql           ( toSqlKey
                                                , fromSqlKey
                                                )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Text.Encoding             ( decodeUtf8
                                                , encodeUtf8
                                                )
import           Data.Functor                   ( (<&>) )
import           Data.ByteString                ( ByteString )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Text.Printf                    ( printf )
import           Text.Read                      ( readMaybe )
import           Frankie

import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Binah.Updates
import           Binah.Insert
import           Model

import           Helpers
import           Controllers

import           Control.Monad                  ( when )


------------------------------------------------------------------------------------------------
-- | Edit Review
------------------------------------------------------------------------------------------------

data EditReview = EditReview ReviewId ReviewData | NewReview PaperId

instance TemplateData EditReview where
  templateFile = "review.edit.html.mustache"

  toMustache (NewReview paperId) = Mustache.object ["action" ~> newReviewRoute paperId]
  toMustache (EditReview reviewId review) =
    Mustache.object ["action" ~> reviewEditRoute reviewId, "review" ~> review]

{-@ reviewNew :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
reviewNew :: Int64 -> Controller ()
reviewNew pid = do
  let paperId = toSqlKey pid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  _        <- checkPcOr forbidden viewer
  _        <- checkStageOr forbidden "review"
  req      <- request
  if reqMethod req == methodPost
    then do
      _ <- selectFirstOr
        forbidden
        (reviewAssignmentPaper' ==. paperId &&: reviewAssignmentUser' ==. viewerId)
      params <- parseForm
      let score = lookup "score" params >>= readMaybe . Text.unpack
      case (score, lookup "content" params) of
        (Just score, Just content) -> do
          reviewId <- insert (mkReview paperId viewerId content score)
          respondTagged (redirectTo (reviewRoute reviewId))
        _ -> respondTagged badRequest
    else respondTagged forbidden


------------------------------------------------------------------------------------------------
-- | Show Review
------------------------------------------------------------------------------------------------

newtype ShowReview = ShowReview ReviewData

instance TemplateData ShowReview where
  templateFile = "review.show.html.mustache"

  toMustache (ShowReview review) = Mustache.object ["review" ~> review]

{-@ updateReview :: _ -> TaggedT<{\_ -> True}, {\_ -> True}> _ _ @-}
updateReview :: ReviewId -> Controller ()
updateReview reviewId = do
  viewer <- requireAuthUser
  isPC   <- pc viewer

  when (not isPC || currentStage /= "review") (respondTagged forbidden)

  params <- parseForm
  case lookup "content" params of
    Just content -> updateWhere (reviewId' ==. reviewId) (reviewContent' `assign` content)
    Nothing      -> return ()

  case lookup "score" params of
    Just score -> updateWhere (reviewId' ==. reviewId) (reviewScore' `assign` read (show score))
    Nothing    -> return ()

{-@ reviewShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
reviewShow :: Int64 -> Controller ()
reviewShow rid = do
  let reviewId = toSqlKey rid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer

  req      <- request

  when (reqMethod req == methodPost) (updateReview reviewId)

  review <- selectFirstOr404 (reviewId' ==. reviewId)
  isPC   <- pc viewer
  case (isPC, currentStage == "public") of
    (True, _) -> do
      reviewData <- project2 (reviewScore', reviewContent') review
      respondHtml $ ShowReview (uncurry ReviewData reviewData)
    (_, True) -> do
      paperId <- project reviewPaper' review
      paper   <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. viewerId)
      case paper of
        Just _ -> do
          reviewData <- project2 (reviewScore', reviewContent') review
          respondHtml $ ShowReview (uncurry ReviewData reviewData)
        Nothing -> return ()
    _ -> return ()

  respondTagged forbidden


------------------------------------------------------------------------------------------------
-- | Helpers
------------------------------------------------------------------------------------------------

data ReviewData = ReviewData { reviewDataScore :: Int, reviewDataContent :: Text}

instance ToMustache ReviewData where
  toMustache (ReviewData score content) = Mustache.object ["score" ~> score, "content" ~> content]

reviewRoute :: ReviewId -> ByteString
reviewRoute reviewId = encodeUtf8 (Text.pack path)
  where path = printf "/review/%d/edit" (fromSqlKey reviewId)

reviewEditRoute :: ReviewId -> String
reviewEditRoute reviewId = printf "/review/%d/edit" (fromSqlKey reviewId)

newReviewRoute :: PaperId -> String
newReviewRoute paperId = printf "/paper/%d/review" (fromSqlKey paperId)
