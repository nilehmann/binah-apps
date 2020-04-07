{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.AssignmentShow where

import           Database.Persist.Sql           ( toSqlKey )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
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
import           Model

import           Controllers
import           Helpers

data AssignmentData = AssignmentData { assignmentDataDescription :: Text }

instance TemplateData AssignmentData where
  templateFile = "assignment.show.html.mustache"

instance ToMustache AssignmentData where
  toMustache (AssignmentData description) =
    Mustache.object ["description" ~> toMustache description]


{-@ assignmentShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
assignmentShow :: Int64 -> Controller ()
assignmentShow aid = do
  let assignmentId = toSqlKey aid
  viewer          <- requireAuthUser
  viewerId        <- project userId' viewer
  maybeAssignment <- selectFirst (assignmentId' ==. assignmentId)

  assignment      <- case maybeAssignment of
    Just assignment -> returnTagged assignment
    Nothing         -> respondTagged notFound

  courseId   <- project assignmentCourse' assignment

  enrollment <- selectFirst
    (enrollmentStudent' ==. viewerId &&: enrollmentCourse' ==. courseId)
  instruction <- selectFirst
    (courseInstructorInstructor' ==. viewerId &&: courseInstructorCourse' ==. courseId)
  description <- case (enrollment, instruction) of
    (Just _, _) -> project assignmentDescription' assignment
    (_, Just _) -> project assignmentDescription' assignment
    _           -> respondTagged forbidden

  respondHtml (AssignmentData description)
