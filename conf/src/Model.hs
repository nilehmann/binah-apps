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

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

{-@ measure isAuthor :: UserId -> PaperId -> Bool @-}

{-@ measure isAccepted :: PaperId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

{-@ predicate IsChair USER = userLevel (entityVal USER) == "chair" @-}

{-@ predicate IsPc USER = userLevel (entityVal USER) == "pc" || userLevel (entityVal USER) == "chair" @-}

{-@ predicate ChairOrSelf USER VIEWER = IsChair VIEWER || entityKey VIEWER == entityKey USER @-}

{-@ predicate PcOrPublic ROW VIEWER = IsPc VIEWER || currentStage == PublicStage @-}

{-@ predicate PcOrAuthorOrAccepted PAPER VIEWER = IsPc VIEWER || isAuthor (entityKey VIEWER) (entityKey PAPER) || (currentStage == PublicStage && paperAccepted (entityVal PAPER)) @-}

{-@ predicate PcOrAuthorOrAccepted' COAUTHOR VIEWER = IsPc VIEWER || isAuthor (entityKey VIEWER) (paperCoauthorPaper (entityVal COAUTHOR)) || (currentStage == PublicStage && isAccepted (paperCoauthorPaper (entityVal COAUTHOR))) @-}

{-@ predicate OnlyPc ROW VIEWER = IsPc VIEWER @-}

{-@ predicate PcOrAuthorIfPublic REVIEW VIEWER = IsPc VIEWER || (currentStage == PublicStage && isAuthor (entityKey VIEWER) (reviewPaper (entityVal REVIEW))) @-}

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

-- * User

{-@ data User = User
  { userUsername :: _
  , userName :: _
  , userEmail :: _
  , userAffiliation :: _
  , userLevel :: _
  }
@-}



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

{-@ assume userName' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userEmail' :: EntityFieldWrapper <
    {\row viewer -> ChairOrSelf row viewer}
  , {\row field  -> field == userEmail (entityVal row)}
  , {\field row  -> field == userEmail (entityVal row)}
  > _ _
@-}
userEmail' :: EntityFieldWrapper User Text
userEmail' = EntityFieldWrapper UserEmail

{-@ assume userAffiliation' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userAffiliation (entityVal row)}
  , {\field row  -> field == userAffiliation (entityVal row)}
  > _ _
@-}
userAffiliation' :: EntityFieldWrapper User Text
userAffiliation' = EntityFieldWrapper UserAffiliation

{-@ assume userLevel' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == userLevel (entityVal row)}
  , {\field row  -> field == userLevel (entityVal row)}
  > _ _
@-}
userLevel' :: EntityFieldWrapper User String
userLevel' = EntityFieldWrapper UserLevel

-- * Paper

{-@ data Paper = Paper
  { paperAuthor :: _
  , paperTitle :: _
  , paperAbstract :: _
  , paperAccepted :: _
  }
@-}

{-@ invariant {v: Entity Paper | isAuthor (paperAuthor (entityVal v)) (entityKey v)} @-}

{-@ invariant {v: Entity Paper | (paperAccepted (entityVal v)) => isAccepted (entityKey v)} @-}

{-@ assume paperId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
paperId' :: EntityFieldWrapper Paper PaperId
paperId' = EntityFieldWrapper PaperId

{-@ assume paperAuthor' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorOrAccepted row viewer}
  , {\row field  -> field == paperAuthor (entityVal row)}
  , {\field row  -> field == paperAuthor (entityVal row)}
  > _ _
@-}
paperAuthor' :: EntityFieldWrapper Paper UserId
paperAuthor' = EntityFieldWrapper PaperAuthor

{-@ assume paperTitle' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorOrAccepted row viewer}
  , {\row field  -> field == paperTitle (entityVal row)}
  , {\field row  -> field == paperTitle (entityVal row)}
  > _ _
@-}
paperTitle' :: EntityFieldWrapper Paper Text
paperTitle' = EntityFieldWrapper PaperTitle

{-@ assume paperAbstract' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorOrAccepted row viewer}
  , {\row field  -> field == paperAbstract (entityVal row)}
  , {\field row  -> field == paperAbstract (entityVal row)}
  > _ _
@-}
paperAbstract' :: EntityFieldWrapper Paper Text
paperAbstract' = EntityFieldWrapper PaperAbstract

{-@ assume paperAccepted' :: EntityFieldWrapper <
    {\row viewer -> PcOrPublic row viewer}
  , {\row field  -> field == paperAccepted (entityVal row)}
  , {\field row  -> field == paperAccepted (entityVal row)}
  > _ _
@-}
paperAccepted' :: EntityFieldWrapper Paper Bool
paperAccepted' = EntityFieldWrapper PaperAccepted

-- * PaperCoauthor

{-@ data PaperCoauthor = PaperCoauthor
  { paperCoauthorPaper :: _
  , paperCoauthorAuthor :: _
  }
@-}



{-@ assume paperCoauthorId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
paperCoauthorId' :: EntityFieldWrapper PaperCoauthor PaperCoauthorId
paperCoauthorId' = EntityFieldWrapper PaperCoauthorId

{-@ assume paperCoauthorPaper' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorOrAccepted' row viewer}
  , {\row field  -> field == paperCoauthorPaper (entityVal row)}
  , {\field row  -> field == paperCoauthorPaper (entityVal row)}
  > _ _
@-}
paperCoauthorPaper' :: EntityFieldWrapper PaperCoauthor PaperId
paperCoauthorPaper' = EntityFieldWrapper PaperCoauthorPaper

{-@ assume paperCoauthorAuthor' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorOrAccepted' row viewer}
  , {\row field  -> field == paperCoauthorAuthor (entityVal row)}
  , {\field row  -> field == paperCoauthorAuthor (entityVal row)}
  > _ _
@-}
paperCoauthorAuthor' :: EntityFieldWrapper PaperCoauthor Text
paperCoauthorAuthor' = EntityFieldWrapper PaperCoauthorAuthor

-- * ReviewAssignment

{-@ data ReviewAssignment = ReviewAssignment
  { reviewAssignmentPaper :: _
  , reviewAssignmentUser :: _
  , reviewAssignmentAssignType :: _
  }
@-}



{-@ assume reviewAssignmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
reviewAssignmentId' :: EntityFieldWrapper ReviewAssignment ReviewAssignmentId
reviewAssignmentId' = EntityFieldWrapper ReviewAssignmentId

{-@ assume reviewAssignmentPaper' :: EntityFieldWrapper <
    {\row viewer -> OnlyPc row viewer}
  , {\row field  -> field == reviewAssignmentPaper (entityVal row)}
  , {\field row  -> field == reviewAssignmentPaper (entityVal row)}
  > _ _
@-}
reviewAssignmentPaper' :: EntityFieldWrapper ReviewAssignment PaperId
reviewAssignmentPaper' = EntityFieldWrapper ReviewAssignmentPaper

{-@ assume reviewAssignmentUser' :: EntityFieldWrapper <
    {\row viewer -> OnlyPc row viewer}
  , {\row field  -> field == reviewAssignmentUser (entityVal row)}
  , {\field row  -> field == reviewAssignmentUser (entityVal row)}
  > _ _
@-}
reviewAssignmentUser' :: EntityFieldWrapper ReviewAssignment UserId
reviewAssignmentUser' = EntityFieldWrapper ReviewAssignmentUser

{-@ assume reviewAssignmentAssignType' :: EntityFieldWrapper <
    {\row viewer -> OnlyPc row viewer}
  , {\row field  -> field == reviewAssignmentAssignType (entityVal row)}
  , {\field row  -> field == reviewAssignmentAssignType (entityVal row)}
  > _ _
@-}
reviewAssignmentAssignType' :: EntityFieldWrapper ReviewAssignment Text
reviewAssignmentAssignType' = EntityFieldWrapper ReviewAssignmentAssignType

-- * Review

{-@ data Review = Review
  { reviewPaper :: _
  , reviewReviewer :: _
  , reviewContent :: _
  , reviewScore :: _
  }
@-}



{-@ assume reviewId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
reviewId' :: EntityFieldWrapper Review ReviewId
reviewId' = EntityFieldWrapper ReviewId

{-@ assume reviewPaper' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorIfPublic row viewer}
  , {\row field  -> field == reviewPaper (entityVal row)}
  , {\field row  -> field == reviewPaper (entityVal row)}
  > _ _
@-}
reviewPaper' :: EntityFieldWrapper Review PaperId
reviewPaper' = EntityFieldWrapper ReviewPaper

{-@ assume reviewReviewer' :: EntityFieldWrapper <
    {\row viewer -> OnlyPc row viewer}
  , {\row field  -> field == reviewReviewer (entityVal row)}
  , {\field row  -> field == reviewReviewer (entityVal row)}
  > _ _
@-}
reviewReviewer' :: EntityFieldWrapper Review UserId
reviewReviewer' = EntityFieldWrapper ReviewReviewer

{-@ assume reviewContent' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorIfPublic row viewer}
  , {\row field  -> field == reviewContent (entityVal row)}
  , {\field row  -> field == reviewContent (entityVal row)}
  > _ _
@-}
reviewContent' :: EntityFieldWrapper Review Text
reviewContent' = EntityFieldWrapper ReviewContent

{-@ assume reviewScore' :: EntityFieldWrapper <
    {\row viewer -> PcOrAuthorIfPublic row viewer}
  , {\row field  -> field == reviewScore (entityVal row)}
  , {\field row  -> field == reviewScore (entityVal row)}
  > _ _
@-}
reviewScore' :: EntityFieldWrapper Review Int
reviewScore' = EntityFieldWrapper ReviewScore


--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------

{-@ data Stage = SubmitStage | ReviewStage | PublicStage @-}
data Stage = SubmitStage | ReviewStage | PublicStage deriving Eq

{-@ inline currentStage @-}
currentStage :: Stage
currentStage = ReviewStage
