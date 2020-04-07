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

data PaperData = PaperData
  { paperDataTitle :: Text
  , paperDataAbstract :: Text
  , paperDataAuthors :: [Text]
  , reviews :: [ReviewData]
  }

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
  p: _ ->
  TaggedT<{\v -> IsPc v ||
                 (currentStage == PublicStage && isAuthor (entityKey v) (entityKey p))},
          {\_ -> False}> _ _ @-}
getReviews :: Entity Paper -> Controller [ReviewData]
getReviews paper = do
  paperId     <- project paperId' paper
  reviews     <- selectList (reviewPaper' ==. paperId)
  reviewsData <- projectList2 (reviewScore', reviewContent') reviews
  return $ map (uncurry ReviewData) reviewsData

{-@ getAuthors :: p: _ -> TaggedT<{\u -> PcOrAuthorOrAccepted p u}, {\_ -> False}> _ _ @-}
getAuthors :: Entity Paper -> Controller [Text]
getAuthors paper = do
  (paperId, authorId) <- project2 (paperId', paperAuthor') paper

  author              <- selectList (userId' ==. authorId)
  authors             <- projectList userName' author

  coauthors           <- selectList (paperCoauthorPaper' ==. paperId)
  coauthorNames       <- projectList paperCoauthorAuthor' coauthors

  return $ authors ++ coauthorNames


{-@ paperShow :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperShow :: Int64 -> Controller ()
paperShow pid = do
  let paperId = toSqlKey pid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  isPC     <- pc viewer

  myPaper  <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. viewerId)
  case myPaper of
    Nothing    -> return ()
    Just paper -> do
      authors <- getAuthors paper
      reviews <- if currentStage == PublicStage then getReviews paper else return []
      (title, abstract) <- project2 (paperTitle', paperAbstract') paper
      respondHtml $ PaperData title abstract authors reviews

  maybePaper <- selectFirst (paperId' ==. paperId)
  case maybePaper of
    Nothing    -> respondTagged notFound
    Just paper -> do
      isPC              <- pc viewer
      authors           <- if isPC then getAuthors paper else return []
      reviews           <- if isPC then getReviews paper else return []
      (title, abstract) <- if isPC
        then project2 (paperTitle', paperAbstract') paper
        else if currentStage == PublicStage
          then do
            accepted <- project paperAccepted' paper
            if accepted then project2 (paperTitle', paperAbstract') paper else return ("", "")
          else return ("", "")

      respondHtml $ PaperData title abstract authors reviews
