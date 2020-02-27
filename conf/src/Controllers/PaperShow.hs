{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.PaperShow where

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


data ReviewData = ReviewData { reviewDataScore :: Int, reviewDataContent :: Text}

data PaperData = PaperData { paperDataTitle :: Text, paperDataAbstract :: Text, paperDataAuthors :: [Text], reviews :: [ReviewData] }

instance TemplateData PaperData where
  templateFile = "paper.show.html.mustache"


instance ToMustache ReviewData where
  toMustache (ReviewData score content) = Mustache.object ["score" ~> score, "content" ~> content]

instance ToMustache PaperData where
  toMustache (PaperData title abstract authors reviews) = Mustache.object
    [ "title" ~> toMustache title
    , "abstract" ~> toMustache abstract
    , "authors" ~> toMustache authors
    , "reviews" ~> toMustache reviews
    ]

{-@ getReviews ::
  paper: _ ->
  TaggedT<{\u -> IsPC u || (currentStage == PublicStage && isAuthor (entityKey u) paper)}, {\_ -> False}> _ _
@-}
getReviews :: PaperId -> Controller [ReviewData]
getReviews paperId = do
  reviews     <- selectList (reviewPaper' ==. paperId)
  reviewsData <- projectList2 (reviewScore', reviewContent') reviews
  returnTagged $ map (uncurry ReviewData) reviewsData

{-@ getAuthors ::
  {v: _ | IsPublic (entityKey v) || isAuthor (entityKey currentUser) (entityKey v) || IsPC currentUser} ->
  TaggedT<{\u -> u == currentUser}, {\_ -> False}> _ _
@-}
getAuthors :: Entity Paper -> Controller [Text]
getAuthors paper = do
  (paperId, authorId) <- project2 (paperId', paperAuthor') paper

  author              <- selectList (userId' ==. authorId)
  authors             <- projectList userName' author

  coauthors           <- selectList (paperCoauthorPaper' ==. paperId)
  coauthorNames       <- projectList paperCoauthorAuthor' coauthors

  returnTagged $ authors ++ coauthorNames


{-@ paperShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperShow :: Int64 -> Controller ()
paperShow pid = do
  let paperId = toSqlKey pid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  isPC     <- pc viewer

  myPaper  <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. viewerId)
  case myPaper of
    Nothing    -> returnTagged ()
    Just paper -> do
      authors <- getAuthors paper
      reviews <- if currentStage == PublicStage then getReviews paperId else returnTagged []
      (title, abstract) <- project2 (paperTitle', paperAbstract') paper
      respondHtml $ PaperData title abstract authors reviews

  maybePaper <- selectFirst (paperId' ==. paperId)
  case maybePaper of
    Nothing    -> respondTagged notFound
    Just paper -> do
      isPC              <- pc viewer
      authors           <- if isPC then getAuthors paper else returnTagged []
      reviews           <- if isPC then getReviews paperId else returnTagged []
      (title, abstract) <- if isPC
        then project2 (paperTitle', paperAbstract') paper
        else if currentStage == PublicStage
          then do
            accepted <- project paperAccepted' paper
            if accepted then project2 (paperTitle', paperAbstract') paper else returnTagged ("", "")
          else returnTagged ("", "")

      respondHtml $ PaperData title abstract authors reviews

