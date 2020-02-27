{-
predicate isInstructor :: UserId -> CourseId -> Bool
predicate isEnrolled   :: UserId -> CoruseId -> Bool

User
  username Text
  email Text {\viewer -> viewer == u}
  name Text
  role String

Course
  name Text

row: CourseInstructor
  course: CourseId
  instructor: UserId

  assert (isInstructor (courseInstructorInstructor row) (courseInstructorCourse row))

row: StudentCourse
  student UserId
  course CourseId
  grade String {\viewer -> (entityKey viewer) == (studentCourseStudent row) || isInstructor (entityKey viewer) (studentCourseCourse row)}

  assert (isEnrolled (studentCourseStudent row) (studentCourseCourse row))

row: Assignment
  name Text
  owner UserId
  course CourseId
  description Text

row: Submission
  assignment AssignmentId
  course  CourseId
  author  UserId
  content Text   {\viewer -> submissionAuthor row == entityKey viewer || isInstructor (entityKey viewer) (submissionCourse row)}
  grade   String {\viewer -> submissionAuthor row == entityKey viewer || isInstructor (entityKey viewer) (submissionCourse row)}
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Model where

import           Database.Persist               ( Key )
import           Database.Persist.TH            ( share
                                                , mkMigrate
                                                , mkPersist
                                                , sqlSettings
                                                , persistLowerCase
                                                )
import           Data.Text                      ( Text )
import qualified Database.Persist              as Persist

import           Binah.Core

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  username Text
  email Text
  name Text
  role String

Course
  name Text

CourseInstructor
  course CourseId
  instructor UserId

StudentCourse
  student UserId
  course CourseId
  grade String

Assignment
  name Text
  owner UserId
  course CourseId
  description Text


Submission
  assignment AssignmentId
  course CourseId
  author UserId
  content Text
  grade String
|]

{-@
data EntityFieldWrapper record typ < policy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   > = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

----------------------------------------------------------------------------------------
-- * Predicates
----------------------------------------------------------------------------------------
{-@ measure isInstructor :: UserId -> CourseId -> Bool @-}
{-@ measure isEnrolled :: UserId -> CourseId -> Bool @-}

----------------------------------------------------------------------------------------
-- * User
----------------------------------------------------------------------------------------

{-@
data User = User
  { userUsername :: _
  , userEmail    :: _
  , userName     :: _
  , userRole     :: _
  }
@-}

{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ assume userUsername' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userUsername (entityVal row)}
  , {\field row -> field == userUsername (entityVal row)}
  > _ _
@-}
userUsername' :: EntityFieldWrapper User Text
userUsername' = EntityFieldWrapper UserUsername

{-@ assume userEmail' :: EntityFieldWrapper <
    {\row viewer -> viewer == row}
  , {\row field -> field == userEmail (entityVal row)}
  , {\field row -> field == userEmail (entityVal row)}
  > _ _
@-}
userEmail' :: EntityFieldWrapper User Text
userEmail' = EntityFieldWrapper UserEmail

{-@ assume userName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userName (entityVal row)}
  , {\field row -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userRole' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userRole (entityVal row)}
  , {\field row -> field == userRole (entityVal row)}
  > _ _
@-}
userRole' :: EntityFieldWrapper User String
userRole' = EntityFieldWrapper UserRole

----------------------------------------------------------------------------------------
-- * Course
----------------------------------------------------------------------------------------

{-@ data Course = Course { courseName :: _ } @-}

{-@ assume courseId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
courseId' :: EntityFieldWrapper Course CourseId
courseId' = EntityFieldWrapper CourseId

{-@ assume courseName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == courseName (entityVal row)}
  , {\field row -> field == courseName (entityVal row)}
  > _ _
@-}
courseName' :: EntityFieldWrapper Course Text
courseName' = EntityFieldWrapper CourseName

----------------------------------------------------------------------------------------
-- * CourseInstructor
----------------------------------------------------------------------------------------

{-@
data CourseInstructor = CourseInstructor
  { courseInstructorCourse     :: _
  , courseInstructorInstructor :: _
  }
@-}

{-@ assume courseInstructorId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
courseInstructorId' :: EntityFieldWrapper CourseInstructor CourseInstructorId
courseInstructorId' = EntityFieldWrapper CourseInstructorId

{-@ assume courseInstructorCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == courseInstructorCourse (entityVal row)}
  , {\field row -> field == courseInstructorCourse (entityVal row)}
  > _ _
@-}
courseInstructorCourse' :: EntityFieldWrapper CourseInstructor CourseId
courseInstructorCourse' = EntityFieldWrapper CourseInstructorCourse

{-@ assume courseInstructorInstructor' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == courseInstructorInstructor (entityVal row)}
  , {\field row -> field == courseInstructorInstructor (entityVal row)}
  > _ _
@-}
courseInstructorInstructor' :: EntityFieldWrapper CourseInstructor UserId
courseInstructorInstructor' = EntityFieldWrapper CourseInstructorInstructor

{-@ invariant {v: Entity CourseInstructor | isInstructor (courseInstructorInstructor (entityVal v)) (courseInstructorCourse (entityVal v))} @-}

----------------------------------------------------------------------------------------
-- * StudentCourse
----------------------------------------------------------------------------------------

{-@
data StudentCourse = StudentCourse
  { studentCourseStudent :: _
  , studentCourseCourse  :: _
  , studentCourseGrade   :: _
  }
@-}

{-@ assume studentCourseId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
studentCourseId' :: EntityFieldWrapper StudentCourse StudentCourseId
studentCourseId' = EntityFieldWrapper StudentCourseId

{-@ assume studentCourseStudent' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == studentCourseStudent (entityVal row)}
  , {\field row -> field == studentCourseStudent (entityVal row)}
  > _ _
@-}
studentCourseStudent' :: EntityFieldWrapper StudentCourse UserId
studentCourseStudent' = EntityFieldWrapper StudentCourseStudent

{-@ assume studentCourseCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == studentCourseCourse (entityVal row)}
  , {\field row -> field == studentCourseCourse (entityVal row)}
  > _ _
@-}
studentCourseCourse' :: EntityFieldWrapper StudentCourse CourseId
studentCourseCourse' = EntityFieldWrapper StudentCourseCourse

{-@ assume studentCourseGrade' :: EntityFieldWrapper <
    {\row viewer -> entityKey viewer == studentCourseStudent (entityVal row) || isInstructor (studentCourseStudent (entityVal row)) (studentCourseCourse (entityVal row))}
  , {\row field -> field == studentCourseGrade (entityVal row)}
  , {\field row -> field == studentCourseGrade (entityVal row)}
  > _ _
@-}
studentCourseGrade' :: EntityFieldWrapper StudentCourse String
studentCourseGrade' = EntityFieldWrapper StudentCourseGrade

{-@ invariant {v: Entity StudentCourse | isEnrolled (studentCourseStudent (entityVal v)) (studentCourseCourse (entityVal v))} @-}

----------------------------------------------------------------------------------------
-- * Assignment
----------------------------------------------------------------------------------------

{-@
data Assignment = Assignment
  { assignmentName        :: _
  , assignmentOwner       :: _
  , assignmentCourse      :: _
  , assignmentDescription :: _
  }
@-}

{-@ assume assignmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
assignmentId' :: EntityFieldWrapper Assignment AssignmentId
assignmentId' = EntityFieldWrapper AssignmentId

{-@ assume assignmentName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == assignmentName (entityVal row)}
  , {\field row -> field == assignmentName (entityVal row)}
  > _ _
@-}
assignmentName' :: EntityFieldWrapper Assignment Text
assignmentName' = EntityFieldWrapper AssignmentName

{-@ assume assignmentOwner' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == assignmentOwner (entityVal row)}
  , {\field row -> field == assignmentOwner (entityVal row)}
  > _ _
@-}
assignmentOwner' :: EntityFieldWrapper Assignment UserId
assignmentOwner' = EntityFieldWrapper AssignmentOwner

{-@ assume assignmentCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == assignmentCourse (entityVal row)}
  , {\field row -> field == assignmentCourse (entityVal row)}
  > _ _
@-}
assignmentCourse' :: EntityFieldWrapper Assignment CourseId
assignmentCourse' = EntityFieldWrapper AssignmentCourse

{-@ assume assignmentDescription' :: EntityFieldWrapper <
    {\row viewer -> isInstructor (entityKey viewer) (assignmentCourse (entityVal row)) || isEnrolled (entityKey viewer) (assignmentCourse (entityVal row))}
  , {\row field -> field == assignmentDescription (entityVal row)}
  , {\field row -> field == assignmentDescription (entityVal row)}
  > _ _
@-}
assignmentDescription' :: EntityFieldWrapper Assignment Text
assignmentDescription' = EntityFieldWrapper AssignmentDescription

----------------------------------------------------------------------------------------
-- * Submission
----------------------------------------------------------------------------------------

{-@
data Submission = Submission
  { submissionAssignment :: _
  , submissionCourse     :: _
  , submissionAuthor     :: _
  , submissionContent    :: _
  , submissionGrade      :: _
  }
@-}

{-@ assume submissionId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
submissionId' :: EntityFieldWrapper Submission SubmissionId
submissionId' = EntityFieldWrapper SubmissionId

{-@ assume submissionAssignment' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == submissionAssignment (entityVal row)}
  , {\field row -> field == submissionAssignment (entityVal row)}
  > _ _
@-}
submissionAssignment' :: EntityFieldWrapper Submission AssignmentId
submissionAssignment' = EntityFieldWrapper SubmissionAssignment

{-@ assume submissionCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == submissionCourse (entityVal row)}
  , {\field row -> field == submissionCourse (entityVal row)}
  > _ _
@-}
submissionCourse' :: EntityFieldWrapper Submission CourseId
submissionCourse' = EntityFieldWrapper SubmissionCourse

{-@ assume submissionAuthor' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == submissionAuthor (entityVal row)}
  , {\field row -> field == submissionAuthor (entityVal row)}
  > _ _
@-}
submissionAuthor' :: EntityFieldWrapper Submission UserId
submissionAuthor' = EntityFieldWrapper SubmissionAuthor

{-@ assume submissionContent' :: EntityFieldWrapper <
    {\row viewer -> submissionAuthor (entityVal row) == entityKey viewer || isInstructor (entityKey viewer) (submissionCourse (entityVal row))}
  , {\row field -> field == submissionContent (entityVal row)}
  , {\field row -> field == submissionContent (entityVal row)}
  > _ _
@-}
submissionContent' :: EntityFieldWrapper Submission Text
submissionContent' = EntityFieldWrapper SubmissionContent

{-@ assume submissionGrade' :: EntityFieldWrapper <
    {\row viewer -> submissionAuthor (entityVal row) == entityKey viewer || isInstructor (entityKey viewer) (submissionCourse (entityVal row))}
  , {\row field -> field == submissionGrade (entityVal row)}
  , {\field row -> field == submissionGrade (entityVal row)}
  > _ _
@-}
submissionGrade' :: EntityFieldWrapper Submission String
submissionGrade' = EntityFieldWrapper SubmissionGrade
