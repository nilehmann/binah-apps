{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--compile-spec" @-}

module Model
  ( currentStage
  , EntityFieldWrapper(..)
  , migrateAll
  , BinahRecord
  , persistentRecord
  , mkUser
  , mkPaper
  , mkReviewAssignment
  , mkReview
  , mkPaperCoauthor
  , User
  , Paper
  , ReviewAssignment
  , Review
  , PaperCoauthor
  , userId'
  , userUsername'
  , userName'
  , userEmail'
  , userAffiliation'
  , userLevel'
  , paperId'
  , paperAuthor'
  , paperTitle'
  , paperAbstract'
  , paperAccepted'
  , reviewAssignmentId'
  , reviewAssignmentPaper'
  , reviewAssignmentUser'
  , reviewAssignmentAssignType'
  , reviewId'
  , reviewPaper'
  , reviewReviewer'
  , reviewContent'
  , reviewScore'
  , paperCoauthorId'
  , paperCoauthorPaper'
  , paperCoauthorAuthor'
  , UserId
  , PaperId
  , ReviewAssignmentId
  , ReviewId
  , PaperCoauthorId
  )
where

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

ReviewAssignment
  paper PaperId
  user UserId
  assignType Text

Review
  paper PaperId
  reviewer UserId
  content Text
  score Int

PaperCoauthor
  paper PaperId
  author Text
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

{-@ measure isReviewer :: UserId -> PaperId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

{-@ predicate IsChair USER = userLevel (entityVal USER) == "chair" @-}

{-@ predicate IsPc USER = userLevel (entityVal USER) == "pc" || userLevel (entityVal USER) == "chair" @-}

{-@ predicate ChairOrSelf USER VIEWER = IsChair VIEWER || entityKey VIEWER == entityKey USER @-}

{-@ predicate PcOrPublic ROW VIEWER = IsPc VIEWER || currentStage == "public" @-}

{-@ predicate PcOrAuthorOrAccepted PAPER VIEWER = IsPc VIEWER || isAuthor (entityKey VIEWER) (entityKey PAPER) || (currentStage == "public" && paperAccepted (entityVal PAPER)) @-}

{-@ predicate PcOrAuthorOrAccepted' COAUTHOR VIEWER = IsPc VIEWER || isAuthor (entityKey VIEWER) (paperCoauthorPaper (entityVal COAUTHOR)) || (currentStage == "public" && isAccepted (paperCoauthorPaper (entityVal COAUTHOR))) @-}

{-@ predicate OnlyPc ROW VIEWER = IsPc VIEWER @-}

{-@ predicate PcOrAuthorIfPublic REVIEW VIEWER = IsPc VIEWER || (currentStage == "public" && isAuthor (entityKey VIEWER) (reviewPaper (entityVal REVIEW))) @-}

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ data BinahRecord record < 
    p :: Entity record -> Bool
  , insertpolicy :: Entity record -> Entity User -> Bool
  , querypolicy  :: Entity record -> Entity User -> Bool 
  >
  = BinahRecord _
@-}
data BinahRecord record = BinahRecord record
{-@ data variance BinahRecord invariant invariant invariant invariant @-}

{-@ persistentRecord :: BinahRecord record -> record @-}
persistentRecord :: BinahRecord record -> record
persistentRecord (BinahRecord record) = record

{-@ measure getJust :: Key record -> Entity record @-}

-- * User

{-@ measure userUsername :: User -> Text @-}
{-@ measure userName :: User -> Text @-}
{-@ measure userEmail :: User -> Text @-}
{-@ measure userAffiliation :: User -> Text @-}
{-@ measure userLevel :: User -> String @-}

{-@ mkUser :: 
     x_0: Text
  -> x_1: Text
  -> x_2: Text
  -> x_3: Text
  -> x_4: String
  -> BinahRecord < 
       {\row -> userUsername (entityVal row) == x_0 && userName (entityVal row) == x_1 && userEmail (entityVal row) == x_2 && userAffiliation (entityVal row) == x_3 && userLevel (entityVal row) == x_4}
     , {\_ _ -> True}
     , {\row viewer -> (IsChair viewer || entityKey viewer == entityKey row)}
     > User
@-}
mkUser x_0 x_1 x_2 x_3 x_4 = BinahRecord (User x_0 x_1 x_2 x_3 x_4)

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
    {\_ _ -> True}
  , {\row field  -> field == userUsername (entityVal row)}
  , {\field row  -> field == userUsername (entityVal row)}
  > _ _
@-}
userUsername' :: EntityFieldWrapper User Text
userUsername' = EntityFieldWrapper UserUsername

{-@ assume userName' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userEmail' :: EntityFieldWrapper <
    {\user viewer -> IsChair viewer || entityKey viewer == entityKey user}
  , {\row field  -> field == userEmail (entityVal row)}
  , {\field row  -> field == userEmail (entityVal row)}
  > _ _
@-}
userEmail' :: EntityFieldWrapper User Text
userEmail' = EntityFieldWrapper UserEmail

{-@ assume userAffiliation' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userAffiliation (entityVal row)}
  , {\field row  -> field == userAffiliation (entityVal row)}
  > _ _
@-}
userAffiliation' :: EntityFieldWrapper User Text
userAffiliation' = EntityFieldWrapper UserAffiliation

{-@ assume userLevel' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userLevel (entityVal row)}
  , {\field row  -> field == userLevel (entityVal row)}
  > _ _
@-}
userLevel' :: EntityFieldWrapper User String
userLevel' = EntityFieldWrapper UserLevel

-- * Paper

{-@ measure paperAuthor :: Paper -> UserId @-}
{-@ measure paperTitle :: Paper -> Text @-}
{-@ measure paperAbstract :: Paper -> Text @-}
{-@ measure paperAccepted :: Paper -> Bool @-}

{-@ mkPaper :: 
     x_0: UserId
  -> x_1: Text
  -> x_2: Text
  -> x_3: Bool
  -> BinahRecord < 
       {\row -> paperAuthor (entityVal row) == x_0 && paperTitle (entityVal row) == x_1 && paperAbstract (entityVal row) == x_2 && paperAccepted (entityVal row) == x_3}
     , {\paper viewer -> paperAuthor (entityVal paper) == entityKey viewer && paperAccepted (entityVal paper) == False && currentStage == "submit"}
     , {\row viewer -> (IsPc viewer || isAuthor (entityKey viewer) (entityKey row) || (currentStage == "public" && paperAccepted (entityVal row))) || (IsPc viewer || currentStage == "public")}
     > Paper
@-}
mkPaper x_0 x_1 x_2 x_3 = BinahRecord (Paper x_0 x_1 x_2 x_3)

{-@ invariant {v: Entity Paper | v == getJust (entityKey v)} @-}

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
    {\paper viewer -> IsPc viewer || isAuthor (entityKey viewer) (entityKey paper) || (currentStage == "public" && paperAccepted (entityVal paper))}
  , {\row field  -> field == paperAuthor (entityVal row)}
  , {\field row  -> field == paperAuthor (entityVal row)}
  > _ _
@-}
paperAuthor' :: EntityFieldWrapper Paper UserId
paperAuthor' = EntityFieldWrapper PaperAuthor

{-@ assume paperTitle' :: EntityFieldWrapper <
    {\paper viewer -> IsPc viewer || isAuthor (entityKey viewer) (entityKey paper) || (currentStage == "public" && paperAccepted (entityVal paper))}
  , {\row field  -> field == paperTitle (entityVal row)}
  , {\field row  -> field == paperTitle (entityVal row)}
  > _ _
@-}
paperTitle' :: EntityFieldWrapper Paper Text
paperTitle' = EntityFieldWrapper PaperTitle

{-@ assume paperAbstract' :: EntityFieldWrapper <
    {\paper viewer -> IsPc viewer || isAuthor (entityKey viewer) (entityKey paper) || (currentStage == "public" && paperAccepted (entityVal paper))}
  , {\row field  -> field == paperAbstract (entityVal row)}
  , {\field row  -> field == paperAbstract (entityVal row)}
  > _ _
@-}
paperAbstract' :: EntityFieldWrapper Paper Text
paperAbstract' = EntityFieldWrapper PaperAbstract

{-@ assume paperAccepted' :: EntityFieldWrapper <
    {\row viewer -> IsPc viewer || currentStage == "public"}
  , {\row field  -> field == paperAccepted (entityVal row)}
  , {\field row  -> field == paperAccepted (entityVal row)}
  > _ _
@-}
paperAccepted' :: EntityFieldWrapper Paper Bool
paperAccepted' = EntityFieldWrapper PaperAccepted

-- * ReviewAssignment

{-@ measure reviewAssignmentPaper :: ReviewAssignment -> PaperId @-}
{-@ measure reviewAssignmentUser :: ReviewAssignment -> UserId @-}
{-@ measure reviewAssignmentAssignType :: ReviewAssignment -> Text @-}

{-@ mkReviewAssignment :: 
     x_0: PaperId
  -> x_1: UserId
  -> x_2: Text
  -> BinahRecord < 
       {\row -> reviewAssignmentPaper (entityVal row) == x_0 && reviewAssignmentUser (entityVal row) == x_1 && reviewAssignmentAssignType (entityVal row) == x_2}
     , {\row viewer -> IsPc viewer && currentStage == "review"}
     , {\row viewer -> (IsPc viewer)}
     > ReviewAssignment
@-}
mkReviewAssignment x_0 x_1 x_2 = BinahRecord (ReviewAssignment x_0 x_1 x_2)

{-@ invariant {v: Entity ReviewAssignment | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity ReviewAssignment | isReviewer (reviewAssignmentUser (entityVal v)) (reviewAssignmentPaper (entityVal v))} @-}

{-@ assume reviewAssignmentId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
reviewAssignmentId' :: EntityFieldWrapper ReviewAssignment ReviewAssignmentId
reviewAssignmentId' = EntityFieldWrapper ReviewAssignmentId

{-@ assume reviewAssignmentPaper' :: EntityFieldWrapper <
    {\row viewer -> IsPc viewer}
  , {\row field  -> field == reviewAssignmentPaper (entityVal row)}
  , {\field row  -> field == reviewAssignmentPaper (entityVal row)}
  > _ _
@-}
reviewAssignmentPaper' :: EntityFieldWrapper ReviewAssignment PaperId
reviewAssignmentPaper' = EntityFieldWrapper ReviewAssignmentPaper

{-@ assume reviewAssignmentUser' :: EntityFieldWrapper <
    {\row viewer -> IsPc viewer}
  , {\row field  -> field == reviewAssignmentUser (entityVal row)}
  , {\field row  -> field == reviewAssignmentUser (entityVal row)}
  > _ _
@-}
reviewAssignmentUser' :: EntityFieldWrapper ReviewAssignment UserId
reviewAssignmentUser' = EntityFieldWrapper ReviewAssignmentUser

{-@ assume reviewAssignmentAssignType' :: EntityFieldWrapper <
    {\row viewer -> IsPc viewer}
  , {\row field  -> field == reviewAssignmentAssignType (entityVal row)}
  , {\field row  -> field == reviewAssignmentAssignType (entityVal row)}
  > _ _
@-}
reviewAssignmentAssignType' :: EntityFieldWrapper ReviewAssignment Text
reviewAssignmentAssignType' = EntityFieldWrapper ReviewAssignmentAssignType

-- * Review

{-@ measure reviewPaper :: Review -> PaperId @-}
{-@ measure reviewReviewer :: Review -> UserId @-}
{-@ measure reviewContent :: Review -> Text @-}
{-@ measure reviewScore :: Review -> Int @-}

{-@ mkReview :: 
     x_0: PaperId
  -> x_1: UserId
  -> x_2: Text
  -> x_3: Int
  -> BinahRecord < 
       {\row -> reviewPaper (entityVal row) == x_0 && reviewReviewer (entityVal row) == x_1 && reviewContent (entityVal row) == x_2 && reviewScore (entityVal row) == x_3}
     , {\review viewer -> currentStage == "review" && reviewReviewer (entityVal review) == entityKey viewer && isReviewer (entityKey viewer) (reviewPaper (entityVal review))}
     , {\row viewer -> (IsPc viewer || (currentStage == "public" && isAuthor (entityKey viewer) (reviewPaper (entityVal row)))) || (IsPc viewer)}
     > Review
@-}
mkReview x_0 x_1 x_2 x_3 = BinahRecord (Review x_0 x_1 x_2 x_3)

{-@ invariant {v: Entity Review | v == getJust (entityKey v)} @-}



{-@ assume reviewId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
reviewId' :: EntityFieldWrapper Review ReviewId
reviewId' = EntityFieldWrapper ReviewId

{-@ assume reviewPaper' :: EntityFieldWrapper <
    {\review viewer -> IsPc viewer || (currentStage == "public" && isAuthor (entityKey viewer) (reviewPaper (entityVal review)))}
  , {\row field  -> field == reviewPaper (entityVal row)}
  , {\field row  -> field == reviewPaper (entityVal row)}
  > _ _
@-}
reviewPaper' :: EntityFieldWrapper Review PaperId
reviewPaper' = EntityFieldWrapper ReviewPaper

{-@ assume reviewReviewer' :: EntityFieldWrapper <
    {\row viewer -> IsPc viewer}
  , {\row field  -> field == reviewReviewer (entityVal row)}
  , {\field row  -> field == reviewReviewer (entityVal row)}
  > _ _
@-}
reviewReviewer' :: EntityFieldWrapper Review UserId
reviewReviewer' = EntityFieldWrapper ReviewReviewer

{-@ assume reviewContent' :: EntityFieldWrapper <
    {\review viewer -> IsPc viewer || (currentStage == "public" && isAuthor (entityKey viewer) (reviewPaper (entityVal review)))}
  , {\row field  -> field == reviewContent (entityVal row)}
  , {\field row  -> field == reviewContent (entityVal row)}
  > _ _
@-}
reviewContent' :: EntityFieldWrapper Review Text
reviewContent' = EntityFieldWrapper ReviewContent

{-@ assume reviewScore' :: EntityFieldWrapper <
    {\review viewer -> IsPc viewer || (currentStage == "public" && isAuthor (entityKey viewer) (reviewPaper (entityVal review)))}
  , {\row field  -> field == reviewScore (entityVal row)}
  , {\field row  -> field == reviewScore (entityVal row)}
  > _ _
@-}
reviewScore' :: EntityFieldWrapper Review Int
reviewScore' = EntityFieldWrapper ReviewScore

-- * PaperCoauthor

{-@ measure paperCoauthorPaper :: PaperCoauthor -> PaperId @-}
{-@ measure paperCoauthorAuthor :: PaperCoauthor -> Text @-}

{-@ mkPaperCoauthor :: 
     x_0: PaperId
  -> x_1: Text
  -> BinahRecord < 
       {\row -> paperCoauthorPaper (entityVal row) == x_0 && paperCoauthorAuthor (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> (IsPc viewer || isAuthor (entityKey viewer) (paperCoauthorPaper (entityVal row)) || (currentStage == "public" && isAccepted (paperCoauthorPaper (entityVal row))))}
     > PaperCoauthor
@-}
mkPaperCoauthor x_0 x_1 = BinahRecord (PaperCoauthor x_0 x_1)

{-@ invariant {v: Entity PaperCoauthor | v == getJust (entityKey v)} @-}



{-@ assume paperCoauthorId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
paperCoauthorId' :: EntityFieldWrapper PaperCoauthor PaperCoauthorId
paperCoauthorId' = EntityFieldWrapper PaperCoauthorId

{-@ assume paperCoauthorPaper' :: EntityFieldWrapper <
    {\coauthor viewer -> IsPc viewer || isAuthor (entityKey viewer) (paperCoauthorPaper (entityVal coauthor)) || (currentStage == "public" && isAccepted (paperCoauthorPaper (entityVal coauthor)))}
  , {\row field  -> field == paperCoauthorPaper (entityVal row)}
  , {\field row  -> field == paperCoauthorPaper (entityVal row)}
  > _ _
@-}
paperCoauthorPaper' :: EntityFieldWrapper PaperCoauthor PaperId
paperCoauthorPaper' = EntityFieldWrapper PaperCoauthorPaper

{-@ assume paperCoauthorAuthor' :: EntityFieldWrapper <
    {\coauthor viewer -> IsPc viewer || isAuthor (entityKey viewer) (paperCoauthorPaper (entityVal coauthor)) || (currentStage == "public" && isAccepted (paperCoauthorPaper (entityVal coauthor)))}
  , {\row field  -> field == paperCoauthorAuthor (entityVal row)}
  , {\field row  -> field == paperCoauthorAuthor (entityVal row)}
  > _ _
@-}
paperCoauthorAuthor' :: EntityFieldWrapper PaperCoauthor Text
paperCoauthorAuthor' = EntityFieldWrapper PaperCoauthorAuthor

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------

{-@ measure currentStage :: String @-}

{-@ assume currentStage :: {v: String | currentStage == v} @-}
currentStage :: String
currentStage = "submit"
