{-
predicate isAuthor :: UserId -> PaperId -> Bool
predicate isAccepted :: PaperId -> Bool
predicate isReviewer :: UserId -> PaperId -> Bool

User
  username Text
  name Text
  email Text       {\viewer -> userLevel viewer == "chair || (entityKey viewer) == self"}
  affiliation Text
  level String

Paper
  author UserId {\viewer -> userLevel viewer == "chair" ||
                            (currentStage == PublicStage && accepted) ||
                            isAuthor (entityKey viewer) self}
  title Text    {\viewer -> userLevel viewer == "chair"
                            isReviewer (entityKey viewer) self ||
                            (currentStage == PublicStage && accepted)
                            isAuthor (entityKey viewer) self}
  abstract Text {\viewer -> userLevel viewer == "chair"
                            isReviewer (entityKey viewer) self ||
                            (currentStage == PublicStage && accepted)
                            isAuthor (entityKey viewer) self}
  accepted Bool {\viewer -> userLevel viewer == "chair" || currentStage == PublicStage}

  assert (isAuthor author self)
  assert (accepted => isAccepted self)

PaperCoauthor
  paper PaperId {\viewer -> userLevel viewer == "chair" ||
                            (currentStage == PublicStage && accepted) ||
                            isAuthor (entityKey viewer) self}
  author Text   {\viewer -> userLevel viewer == "chair" ||
                            (currentStage == PublicStage && accepted) ||
                            isAuthor (entityKey viewer) self}

ReviewAssignment
  paper PaperId   {\viewer -> userLevel viewer == "chair" || (entityKey viewer) == user}
  user UserId     {\viewer -> userLevel viewer == "chair" || (entityKey viewer) == user}
  assignType Text {\viewer -> userLevel viewer == "chair" || (entityKey viewer) == user}

  assert (isReviewer user paper)

Review
  reviewer UserId {\viewer -> userLevel viewer == "chair" || (entityKey viewer) == reviewer}
  paper PaperId   {\viewer -> userLevel viewer == "chair" ||
                              isReviewer (entityKey viewer) paper ||
                              (currentStage == PublicStage && isAuthor (entityKey viewer) paper)}
  content PaperId {\viewer -> userLevel viewer == "chair" ||
                              isReviewer (entityKey viewer) paper ||
                              (currentStage == PublicStage && isAuthor (entityKey viewer) paper)}
  score PaperId   {\viewer -> userLevel viewer == "chair" ||
                              isReviewer (entityKey viewer) paper ||
                              (currentStage == PublicStage && isAuthor (entityKey viewer) paper)}
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
  name Text
  email Text
  affiliation Text
  level String
  deriving Show

Paper
  author UserId
  title Text
  abstract Text
  accepted Bool

PaperCoauthor
  paper PaperId
  author Text

ReviewAssignment
  paper PaperId
  user UserId
  assignType Text

Review
  paper PaperId
  reviewer UserId
  content Text
  score Int
|]

{-@
data EntityFieldWrapper record typ < policy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   > = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}


-- * Predicates
{-@ measure isAuthor :: UserId -> PaperId -> Bool @-}
{-@ measure isAccepted :: PaperId -> Bool @-}
{-@ measure isReviewer :: UserId -> PaperId -> Bool @-}

-- * User

{-@ data User = User
  { userUsername    :: _
  , userName        :: _
  , userEmail       :: _
  , userAffiliation :: _
  , userLevel       :: _
  }
@-}

{-@ predicate IsPC USER = userLevel (entityVal USER) == "chair" || userLevel (entityVal USER) == "pc" @-}
{-@ predicate IsChair USER = userLevel (entityVal USER) == "chair" @-}

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

{-@ assume userName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userName (entityVal row)}
  , {\field row -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userEmail' :: EntityFieldWrapper <
    {\row viewer -> IsChair viewer || (entityKey viewer) == (entityKey row)}
  , {\row field -> field == userEmail (entityVal row)}
  , {\field row -> field == userEmail (entityVal row)}
  > _ _
@-}
userEmail' :: EntityFieldWrapper User Text
userEmail' = EntityFieldWrapper UserEmail

{-@ assume userAffiliation' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userAffiliation (entityVal row)}
  , {\field row -> field == userAffiliation (entityVal row)}
  > _ _
@-}
userAffiliation' :: EntityFieldWrapper User Text
userAffiliation' = EntityFieldWrapper UserAffiliation

{-@ assume userLevel' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == userLevel (entityVal row)}
  , {\field row -> field == userLevel (entityVal row)}
  > _ _
@-}
userLevel' :: EntityFieldWrapper User String
userLevel' = EntityFieldWrapper UserLevel

-- * Paper

{-@ data Paper = Paper
  { paperAuthor   :: _
  , paperTitle    :: _
  , paperAbstract :: _
  , paperAccepted :: _
  }
@-}

{-@ invariant {v: Entity Paper | isAuthor (paperAuthor (entityVal v)) (entityKey v) }@-}
{-@ invariant {v: Entity Paper | paperAccepted (entityVal v) => isAccepted (entityKey v)} @-}
{-@ predicate IsPublic PAPER = currentStage == PublicStage && isAccepted PAPER @-}


{-@ assume paperId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
paperId' :: EntityFieldWrapper Paper PaperId
paperId' = EntityFieldWrapper PaperId

{-@ assume paperAuthor' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        IsPublic (entityKey row) ||
        isAuthor (entityKey viewer) (entityKey row)
    }
  , {\row field -> field == paperAuthor (entityVal row)}
  , {\field row -> field == paperAuthor (entityVal row)}
  > _ _
@-}
paperAuthor' :: EntityFieldWrapper Paper UserId
paperAuthor' = EntityFieldWrapper PaperAuthor

{-@ assume paperTitle' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        isReviewer (entityKey viewer) (entityKey row) ||
        IsPublic (entityKey row) ||
        isAuthor (entityKey viewer) (entityKey row)
    }
  , {\row field -> field == paperTitle (entityVal row)}
  , {\field row -> field == paperTitle (entityVal row)}
  > _ _
@-}
paperTitle' :: EntityFieldWrapper Paper Text
paperTitle' = EntityFieldWrapper PaperTitle

{-@ assume paperAbstract' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        isReviewer (entityKey viewer) (entityKey row) ||
        IsPublic (entityKey row) ||
        isAuthor (entityKey viewer) (entityKey row)
    }
  , {\row field -> field == paperAbstract (entityVal row)}
  , {\field row -> field == paperAbstract (entityVal row)}
  > _ _
@-}
paperAbstract' :: EntityFieldWrapper Paper Text
paperAbstract' = EntityFieldWrapper PaperAbstract

{-@ assume paperAccepted' :: EntityFieldWrapper <
    {\row viewer -> IsPC viewer || currentStage == PublicStage}
  , {\row field -> field == paperAccepted (entityVal row)}
  , {\field row -> field == paperAccepted (entityVal row)}
  > _ _
@-}
paperAccepted' :: EntityFieldWrapper Paper Bool
paperAccepted' = EntityFieldWrapper PaperAccepted

-- * PaperCoauthor

{-@ data PaperCoauthor = PaperCoauthor
  { paperCoauthorPaper  :: _
  , paperCoauthorAuthor :: _
  }
@-}

{-@ assume paperCoauthorId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
paperCoauthorId' :: EntityFieldWrapper PaperCoauthor PaperCoauthorId
paperCoauthorId' = EntityFieldWrapper PaperCoauthorId

{-@ assume paperCoauthorPaper' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        IsPublic (paperCoauthorPaper (entityVal row)) ||
        isAuthor (entityKey viewer) (paperCoauthorPaper (entityVal row))
    }
  , {\row field -> field == paperCoauthorPaper (entityVal row)}
  , {\field row -> field == paperCoauthorPaper (entityVal row)}
  > _ _
@-}
paperCoauthorPaper' :: EntityFieldWrapper PaperCoauthor PaperId
paperCoauthorPaper' = EntityFieldWrapper PaperCoauthorPaper

{-@ assume paperCoauthorAuthor' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        IsPublic (paperCoauthorPaper (entityVal row)) ||
        isAuthor (entityKey viewer) (paperCoauthorPaper (entityVal row))
    }
  , {\row field -> field == paperCoauthorAuthor (entityVal row)}
  , {\field row -> field == paperCoauthorAuthor (entityVal row)}
  > _ _
@-}
paperCoauthorAuthor' :: EntityFieldWrapper PaperCoauthor Text
paperCoauthorAuthor' = EntityFieldWrapper PaperCoauthorAuthor

-- * ReviewAssignment

{-@ data ReviewAssignment = ReviewAssignment
  { reviewAssignmentPaper      :: _
  , reviewAssignmentUser       :: _
  , reviewAssignmentAssignType :: _
  }
@-}

{-@ invariant {v: Entity ReviewAssignment | isReviewer (reviewAssignmentUser (entityVal v)) (reviewAssignmentPaper (entityVal v)) }@-}

{-@ assume reviewAssignmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
reviewAssignmentId' :: EntityFieldWrapper ReviewAssignment ReviewAssignmentId
reviewAssignmentId' = EntityFieldWrapper ReviewAssignmentId

{-@ assume reviewAssignmentPaper' :: EntityFieldWrapper <
    {\row viewer -> IsPC viewer || (entityKey viewer) == (reviewAssignmentUser (entityVal row))}
  , {\row field -> field == reviewAssignmentPaper (entityVal row)}
  , {\field row -> field == reviewAssignmentPaper (entityVal row)}
  > _ _
@-}
reviewAssignmentPaper' :: EntityFieldWrapper ReviewAssignment PaperId
reviewAssignmentPaper' = EntityFieldWrapper ReviewAssignmentPaper

{-@ assume reviewAssignmentUser' :: EntityFieldWrapper <
    {\row viewer -> IsPC viewer || (entityKey viewer) == (reviewAssignmentUser (entityVal row))}
  , {\row field -> field == reviewAssignmentUser (entityVal row)}
  , {\field row -> field == reviewAssignmentUser (entityVal row)}
  > _ _
@-}
reviewAssignmentUser' :: EntityFieldWrapper ReviewAssignment UserId
reviewAssignmentUser' = EntityFieldWrapper ReviewAssignmentUser

{-@ assume reviewAssignmentAssignType' :: EntityFieldWrapper <
    {\row viewer -> IsPC viewer || (entityKey viewer) == (reviewAssignmentUser (entityVal row))}
  , {\row field -> field == reviewAssignmentAssignType (entityVal row)}
  , {\field row -> field == reviewAssignmentAssignType (entityVal row)}
  > _ _
@-}
reviewAssignmentAssignType' :: EntityFieldWrapper ReviewAssignment Text
reviewAssignmentAssignType' = EntityFieldWrapper ReviewAssignmentAssignType

-- * Review

{-@ data Review = Review
  { reviewPaper    :: _
  , reviewReviewer :: _
  , reviewContent  :: _
  , reviewScore    :: _
  }
@-}

{-@ assume reviewId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field -> field == entityKey row}
  , {\field row -> field == entityKey row}
  > _ _
@-}
reviewId' :: EntityFieldWrapper Review ReviewId
reviewId' = EntityFieldWrapper ReviewId

{-@ assume reviewPaper' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        isReviewer (entityKey viewer) (reviewPaper (entityVal row)) ||
        (currentStage == PublicStage && isAuthor (entityKey viewer) (reviewPaper (entityVal row)))
    }
  , {\row field -> field == reviewPaper (entityVal row)}
  , {\field row -> field == reviewPaper (entityVal row)}
  > _ _
@-}
reviewPaper' :: EntityFieldWrapper Review PaperId
reviewPaper' = EntityFieldWrapper ReviewPaper

{-@ assume reviewReviewer' :: EntityFieldWrapper <
    {\row viewer -> IsPC viewer || isReviewer (entityKey viewer) (reviewPaper (entityVal row))}
  , {\row field -> field == reviewReviewer (entityVal row)}
  , {\field row -> field == reviewReviewer (entityVal row)}
  > _ _
@-}
reviewReviewer' :: EntityFieldWrapper Review UserId
reviewReviewer' = EntityFieldWrapper ReviewReviewer

{-@ assume reviewContent' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        isReviewer (entityKey viewer) (reviewPaper (entityVal row)) ||
        (currentStage == PublicStage && isAuthor (entityKey viewer) (reviewPaper (entityVal row)))
    }
  , {\row field -> field == reviewContent (entityVal row)}
  , {\field row -> field == reviewContent (entityVal row)}
  > _ _
@-}
reviewContent' :: EntityFieldWrapper Review Text
reviewContent' = EntityFieldWrapper ReviewContent

{-@ assume reviewScore' :: EntityFieldWrapper <
    {\row viewer ->
        IsPC viewer ||
        isReviewer (entityKey viewer) (reviewPaper (entityVal row)) ||
        (currentStage == PublicStage && isAuthor (entityKey viewer) (reviewPaper (entityVal row)))
    }
  , {\row field -> field == reviewScore (entityVal row)}
  , {\field row -> field == reviewScore (entityVal row)}
  > _ _
@-}
reviewScore' :: EntityFieldWrapper Review Int
reviewScore' = EntityFieldWrapper ReviewScore

{-@ data Stage = SubmitStage | ReviewStage | PublicStage @-}
data Stage = SubmitStage | ReviewStage | PublicStage deriving Eq

{-@ inline currentStage @-}
currentStage :: Stage
currentStage = PublicStage
