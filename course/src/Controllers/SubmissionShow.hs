{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.SubmissionShow where

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
import           Binah.Updates
import           Binah.Frankie
import           Model

import           Controllers
import           Helpers

data SubmissionData = SubmissionData
  { submissionDataContent :: Text
  , submissionDataGrade :: String
  }

instance TemplateData SubmissionData where
  templateFile = "submission.show.html.mustache"

instance ToMustache SubmissionData where
  toMustache (SubmissionData content grade) =
    Mustache.object ["content" ~> toMustache content, "grade" ~> toMustache grade]


-- If I inline this function LH goes crazy
theUpdate :: SubmissionId -> Text -> Controller ()
theUpdate submissionId content = update submissionId (submissionContent' `assign` content)

{-@ submissionShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
submissionShow :: Int64 -> Controller ()
submissionShow sid = do
  let submissionId = toSqlKey sid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer

  req      <- request
  if reqMethod req == methodPost
    then do
      params <- parseForm
      case lookup "content" params of
        Just content -> theUpdate submissionId (decodeUtf8 content)
        Nothing      -> returnTagged ()
    else returnTagged ()

  submission   <- selectFirstOr404 (submissionId' ==. submissionId)
  assignmentId <- project submissionAssignment' submission
  authorId     <- project submissionAuthor' submission
  assignment   <- selectFirstOr404 (assignmentId' ==. assignmentId)
  courseId     <- project assignmentCourse' assignment

  instruction  <- selectFirst
    (courseInstructorInstructor' ==. viewerId &&: courseInstructorCourse' ==. courseId)

  (content, grade) <- case (authorId == viewerId, instruction) of
    (True, _     ) -> project2 (submissionContent', submissionGrade') submission
    (_   , Just _) -> project2 (submissionContent', submissionGrade') submission
    _              -> respondTagged forbidden

  respondHtml (SubmissionData content grade)
