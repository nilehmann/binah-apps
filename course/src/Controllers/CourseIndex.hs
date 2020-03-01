{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.CourseIndex where

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

data CourseIndex = CourseIndex [CourseData]

instance TemplateData CourseIndex where
  templateFile = "course.index.html.mustache"

instance ToMustache CourseIndex where
  toMustache (CourseIndex courses) = Mustache.object ["courses" ~> map toMustache courses]

data CourseData = CourseData
  { courseDataId :: CourseId
  , courseDataName :: Text
  , courseDataGrade :: String
  }

instance ToMustache CourseData where
  toMustache (CourseData id name grade) = Mustache.object
    [ "course_id" ~> toMustache (keyToText id)
    , "name" ~> toMustache name
    , "grade" ~> toMustache grade
    ]

{-@ joinWithCourses :: _ -> TaggedT<{\_ -> True}, {\_ ->False}> _ _ @-}
joinWithCourses :: [(CourseId, String)] -> Controller [CourseData]
joinWithCourses gradesByCourse = do
  courses     <- selectList (courseId' <-. map fst gradesByCourse)
  coursesById <- projectList2 (courseId', courseName') courses
  returnTagged $ innerJoin CourseData coursesById gradesByCourse


{-@ courseIndex :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
courseIndex :: Controller ()
courseIndex = do
  viewer         <- requireAuthUser
  viewerId       <- project userId' viewer
  enrollments    <- selectList (studentCourseStudent' ==. viewerId)
  gradesByCourse <- projectList2 (studentCourseCourse', studentCourseGrade') enrollments
  courses        <- joinWithCourses gradesByCourse
  respondHtml (CourseIndex courses)
