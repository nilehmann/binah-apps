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

Enrollment
  student UserId
  course CourseId
  grade String

Assignment
  name Text
  course CourseId
  description Text

Submission
  assignment AssignmentId
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

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

{-@ measure isInstructor :: UserId -> CourseId -> Bool @-}

{-@ measure isEnrolled :: UserId -> CourseId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

{-@ predicate IsSelf USER VIEWER = entityKey USER == entityKey VIEWER @-}

{-@ predicate StudentOrInstructor ENROLLMENT VIEWER = entityKey VIEWER == enrollmentStudent (entityVal ENROLLMENT) || isInstructor (entityKey VIEWER) (enrollmentCourse (entityVal ENROLLMENT)) @-}

{-@ predicate EnrolledOrInstructor ASSIGNMENT VIEWER = isEnrolled (entityKey VIEWER) (assignmentCourse (entityVal ASSIGNMENT)) || isInstructor (entityKey VIEWER) (assignmentCourse (entityVal ASSIGNMENT)) @-}

{-@ predicate AuthorOrInstructor SUBMISSION VIEWER = submissionAuthor (entityVal SUBMISSION) == entityKey VIEWER || isInstructor (entityKey VIEWER) (assignmentCourse (entityVal (getJust (submissionAssignment (entityVal SUBMISSION))))) @-}

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ measure getJust :: Key record -> Entity record @-}

-- * User

{-@ data User = User
  { userUsername :: _
  , userEmail :: _
  , userName :: _
  , userRole :: _
  }
@-}

{-@ invariant {v: Entity User | v == getJust (entityKey v)} @-}



{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ assume userUsername' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userUsername (entityVal row)}
  , {\field row  -> field == userUsername (entityVal row)}
  > _ _
@-}
userUsername' :: EntityFieldWrapper User Text
userUsername' = EntityFieldWrapper UserUsername

{-@ assume userEmail' :: EntityFieldWrapper <
    {\row viewer -> IsSelf row viewer}
  , {\row field  -> field == userEmail (entityVal row)}
  , {\field row  -> field == userEmail (entityVal row)}
  > _ _
@-}
userEmail' :: EntityFieldWrapper User Text
userEmail' = EntityFieldWrapper UserEmail

{-@ assume userName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userRole' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userRole (entityVal row)}
  , {\field row  -> field == userRole (entityVal row)}
  > _ _
@-}
userRole' :: EntityFieldWrapper User String
userRole' = EntityFieldWrapper UserRole

-- * Course

{-@ data Course = Course
  { courseName :: _
  }
@-}

{-@ invariant {v: Entity Course | v == getJust (entityKey v)} @-}



{-@ assume courseId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
courseId' :: EntityFieldWrapper Course CourseId
courseId' = EntityFieldWrapper CourseId

{-@ assume courseName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == courseName (entityVal row)}
  , {\field row  -> field == courseName (entityVal row)}
  > _ _
@-}
courseName' :: EntityFieldWrapper Course Text
courseName' = EntityFieldWrapper CourseName

-- * CourseInstructor

{-@ data CourseInstructor = CourseInstructor
  { courseInstructorCourse :: _
  , courseInstructorInstructor :: _
  }
@-}

{-@ invariant {v: Entity CourseInstructor | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity CourseInstructor | isInstructor (courseInstructorInstructor (entityVal v)) (courseInstructorCourse (entityVal v))} @-}

{-@ assume courseInstructorId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
courseInstructorId' :: EntityFieldWrapper CourseInstructor CourseInstructorId
courseInstructorId' = EntityFieldWrapper CourseInstructorId

{-@ assume courseInstructorCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == courseInstructorCourse (entityVal row)}
  , {\field row  -> field == courseInstructorCourse (entityVal row)}
  > _ _
@-}
courseInstructorCourse' :: EntityFieldWrapper CourseInstructor CourseId
courseInstructorCourse' = EntityFieldWrapper CourseInstructorCourse

{-@ assume courseInstructorInstructor' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == courseInstructorInstructor (entityVal row)}
  , {\field row  -> field == courseInstructorInstructor (entityVal row)}
  > _ _
@-}
courseInstructorInstructor' :: EntityFieldWrapper CourseInstructor UserId
courseInstructorInstructor' = EntityFieldWrapper CourseInstructorInstructor

-- * Enrollment

{-@ data Enrollment = Enrollment
  { enrollmentStudent :: _
  , enrollmentCourse :: _
  , enrollmentGrade :: _
  }
@-}

{-@ invariant {v: Entity Enrollment | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity Enrollment | isEnrolled (enrollmentStudent (entityVal v)) (enrollmentCourse (entityVal v))} @-}

{-@ assume enrollmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
enrollmentId' :: EntityFieldWrapper Enrollment EnrollmentId
enrollmentId' = EntityFieldWrapper EnrollmentId

{-@ assume enrollmentStudent' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == enrollmentStudent (entityVal row)}
  , {\field row  -> field == enrollmentStudent (entityVal row)}
  > _ _
@-}
enrollmentStudent' :: EntityFieldWrapper Enrollment UserId
enrollmentStudent' = EntityFieldWrapper EnrollmentStudent

{-@ assume enrollmentCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == enrollmentCourse (entityVal row)}
  , {\field row  -> field == enrollmentCourse (entityVal row)}
  > _ _
@-}
enrollmentCourse' :: EntityFieldWrapper Enrollment CourseId
enrollmentCourse' = EntityFieldWrapper EnrollmentCourse

{-@ assume enrollmentGrade' :: EntityFieldWrapper <
    {\row viewer -> StudentOrInstructor row viewer}
  , {\row field  -> field == enrollmentGrade (entityVal row)}
  , {\field row  -> field == enrollmentGrade (entityVal row)}
  > _ _
@-}
enrollmentGrade' :: EntityFieldWrapper Enrollment String
enrollmentGrade' = EntityFieldWrapper EnrollmentGrade

-- * Assignment

{-@ data Assignment = Assignment
  { assignmentName :: _
  , assignmentCourse :: _
  , assignmentDescription :: _
  }
@-}

{-@ invariant {v: Entity Assignment | v == getJust (entityKey v)} @-}



{-@ assume assignmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
assignmentId' :: EntityFieldWrapper Assignment AssignmentId
assignmentId' = EntityFieldWrapper AssignmentId

{-@ assume assignmentName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == assignmentName (entityVal row)}
  , {\field row  -> field == assignmentName (entityVal row)}
  > _ _
@-}
assignmentName' :: EntityFieldWrapper Assignment Text
assignmentName' = EntityFieldWrapper AssignmentName

{-@ assume assignmentCourse' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == assignmentCourse (entityVal row)}
  , {\field row  -> field == assignmentCourse (entityVal row)}
  > _ _
@-}
assignmentCourse' :: EntityFieldWrapper Assignment CourseId
assignmentCourse' = EntityFieldWrapper AssignmentCourse

{-@ assume assignmentDescription' :: EntityFieldWrapper <
    {\row viewer -> EnrolledOrInstructor row viewer}
  , {\row field  -> field == assignmentDescription (entityVal row)}
  , {\field row  -> field == assignmentDescription (entityVal row)}
  > _ _
@-}
assignmentDescription' :: EntityFieldWrapper Assignment Text
assignmentDescription' = EntityFieldWrapper AssignmentDescription

-- * Submission

{-@ data Submission = Submission
  { submissionAssignment :: _
  , submissionAuthor :: _
  , submissionContent :: _
  , submissionGrade :: _
  }
@-}

{-@ invariant {v: Entity Submission | v == getJust (entityKey v)} @-}



{-@ assume submissionId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
submissionId' :: EntityFieldWrapper Submission SubmissionId
submissionId' = EntityFieldWrapper SubmissionId

{-@ assume submissionAssignment' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == submissionAssignment (entityVal row)}
  , {\field row  -> field == submissionAssignment (entityVal row)}
  > _ _
@-}
submissionAssignment' :: EntityFieldWrapper Submission AssignmentId
submissionAssignment' = EntityFieldWrapper SubmissionAssignment

{-@ assume submissionAuthor' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == submissionAuthor (entityVal row)}
  , {\field row  -> field == submissionAuthor (entityVal row)}
  > _ _
@-}
submissionAuthor' :: EntityFieldWrapper Submission UserId
submissionAuthor' = EntityFieldWrapper SubmissionAuthor

{-@ assume submissionContent' :: EntityFieldWrapper <
    {\row viewer -> AuthorOrInstructor row viewer}
  , {\row field  -> field == submissionContent (entityVal row)}
  , {\field row  -> field == submissionContent (entityVal row)}
  > _ _
@-}
submissionContent' :: EntityFieldWrapper Submission Text
submissionContent' = EntityFieldWrapper SubmissionContent

{-@ assume submissionGrade' :: EntityFieldWrapper <
    {\row viewer -> AuthorOrInstructor row viewer}
  , {\row field  -> field == submissionGrade (entityVal row)}
  , {\field row  -> field == submissionGrade (entityVal row)}
  > _ _
@-}
submissionGrade' :: EntityFieldWrapper Submission String
submissionGrade' = EntityFieldWrapper SubmissionGrade

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------


