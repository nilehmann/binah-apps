{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.PaperIndex where

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

import           Helpers
import           Controllers


data PaperIndex = PaperIndex [RowData]

instance TemplateData PaperIndex where
  templateFile = "paper.index.html.mustache"

instance ToMustache PaperIndex where
  toMustache (PaperIndex papers) = Mustache.object ["papers" ~> map toMustache papers]

data RowData = RowData {paperDataAuthorId :: Maybe UserId, paperDataAuthor :: Maybe Text,  paperDataId :: PaperId, paperDataTitle :: Text }

instance ToMustache  RowData where
  toMustache (RowData authorId authorName paperId paperTitle) = Mustache.object
    [ "paper_id" ~> toMustache (keyToText paperId)
    , "author_id" ~> toMustache (fmap keyToText authorId)
    , "title" ~> toMustache paperTitle
    , "author_name" ~> authorName
    ]


{-@ joinWithAuthors :: _ -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
joinWithAuthors :: [(UserId, (PaperId, Text))] -> Controller [RowData]
joinWithAuthors papersByAuthor = do
  authors     <- selectList (userId' <-. map fst papersByAuthor)
  authorsById <- projectList2 (userId', userName') authors

  returnTagged $ innerJoin
    (\authorId (paperId, title) authorName ->
      RowData (Just authorId) (Just authorName) paperId title
    )
    papersByAuthor
    authorsById

{-@ getAllPapers :: TaggedT<{\u -> IsPC u}, {\_ -> False}> _ _ @-}
getAllPapers :: Controller [RowData]
getAllPapers = do
  papers    <- selectList trueF
  authorIds <- projectList paperAuthor' papers
  paperData <- projectList2 (paperId', paperTitle') papers
  joinWithAuthors $ zip authorIds paperData


{-@ getAcceptedPapers :: TaggedT<{\_ -> currentStage == PublicStage}, {\_ -> False}> _ _ @-}
getAcceptedPapers :: Controller [RowData]
getAcceptedPapers = do
  papers    <- selectList (paperAccepted' ==. True)
  authorIds <- projectList paperAuthor' papers
  paperData <- projectList2 (paperId', paperTitle') papers
  joinWithAuthors $ zip authorIds paperData


{-@ getAssignedPapers :: viewer: _ -> TaggedT<{\u -> (entityKey u) == viewer}, {\_ -> False}> _ _  @-}
getAssignedPapers :: UserId -> Controller [RowData]
getAssignedPapers viewerId = do
  myAssignments <- selectList (reviewAssignmentUser' ==. viewerId)
  paperIds      <- projectList reviewAssignmentPaper' myAssignments
  papers        <- selectList (paperId' <-. paperIds)

  paperData     <- projectList2 (paperId', paperTitle') papers
  returnTagged $ map (uncurry $ RowData Nothing Nothing) paperData


{-@ getMyPapers :: viewer: Entity User -> TaggedT<{\u -> (entityKey viewer) == (entityKey u)}, {\_ -> False}> _ _ @-}
getMyPapers :: Entity User -> Controller [RowData]
getMyPapers viewer = do
  viewerId   <- project userId' viewer
  viewerName <- project userName' viewer

  papers     <- selectList (paperAuthor' ==. viewerId)
  paperData  <- projectList2 (paperId', paperTitle') papers

  returnTagged $ map
    (uncurry $ \paperId title -> RowData (Just viewerId) (Just viewerName) paperId title)
    paperData


{-@ paperIndex :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperIndex :: Controller ()
paperIndex = do
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  papers   <- selectList trueF
  paperIds <- projectList paperId' papers
  isPC     <- pc viewer
  papers   <- case (currentStage, isPC) of
    (PublicStage, _   ) -> getAcceptedPapers
    (_          , True) -> getAllPapers
    _                   -> getAssignedPapers viewerId
  respondHtml (PaperIndex papers)
