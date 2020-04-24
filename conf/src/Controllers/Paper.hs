{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers.Paper where

import           Database.Persist.Sql           ( toSqlKey
                                                , fromSqlKey
                                                )
import           Data.Text.Encoding             ( decodeUtf8
                                                , encodeUtf8
                                                )
import           Data.Int                       ( Int64 )
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.ByteString                ( ByteString )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Text.Printf                    ( printf )
import           Frankie


import           Binah.Core
import           Binah.Actions
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie
import           Binah.Insert
import           Binah.Updates
import           Model

import           Helpers
import           Controllers
import           Control.Monad                  ( when )

data PaperNew = PaperNew

instance ToMustache PaperNew where
  toMustache PaperNew = Mustache.object ["action" ~> ("/paper" :: String)]

data PaperEdit = PaperEdit PaperId PaperData

instance ToMustache PaperEdit where
  toMustache (PaperEdit id paper) =
    Mustache.object ["action" ~> paperEditRoute id, "paper" ~> paper]

data ReviewData = ReviewData { reviewDataScore :: Int, reviewDataContent :: Text}

data PaperData = PaperData
  { paperDataId :: PaperId
  , paperDataTitle :: Text
  , paperDataAbstract :: Text
  , paperDataAuthors :: [Text]
  , reviews :: [ReviewData]
  }


instance ToMustache ReviewData where
  toMustache (ReviewData score content) = Mustache.object ["score" ~> score, "content" ~> content]

instance ToMustache PaperData where
  toMustache (PaperData id title abstract authors reviews) = Mustache.object
    [ "id" ~> id
    , "title" ~> title
    , "abstract" ~> abstract
    , "authors" ~> authors
    , "reviews" ~> reviews
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

  myPaper  <- getMyPaper viewerId paperId
  case myPaper of
    Nothing        -> return ()
    Just paperData -> respondHtml "paper.show.html.mustache" paperData

  paper             <- selectFirstOr404 (paperId' ==. paperId)
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

  respondHtml "paper.show.html.mustache" $ PaperData paperId title abstract authors reviews

------------------------------------------------------------------------------------------------
-- | Edit Paper
------------------------------------------------------------------------------------------------

{-@ paperEdit :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperEdit :: Int64 -> Controller ()
paperEdit pid = do
  let paperId = toSqlKey pid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  req      <- request
  when (reqMethod req == methodPost) (updatePaper paperId)
  maybePaper <- getMyPaper viewerId paperId
  case maybePaper of
    Nothing        -> respondTagged notFound
    Just paperData -> respondHtml "paper.edit.html.mustache" (PaperEdit paperId paperData)

{-@ updatePaper :: _ -> TaggedT<{\_ -> True}, {\_ -> True}> _ _ @-}
updatePaper :: PaperId -> Controller ()
updatePaper paperId = do
  params <- parseForm
  case lookup "title" params of
    -- ENFORCE: Viewer is the author of the paper && stage == submit
    Just title -> update paperId (paperTitle' `assign` title)
    Nothing    -> return ()

  case lookup "abstract" params of
    -- ENFORCE: Viewer is the author of the paper && stage == submit
    Just abstract -> update paperId (paperAbstract' `assign` abstract)
    Nothing       -> return ()


------------------------------------------------------------------------------------------------
-- | New Paper
------------------------------------------------------------------------------------------------

{-@ paperNew :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperNew :: Controller ()
paperNew = do
  when (currentStage /= SubmitStage) (respondTagged forbidden)

  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  req      <- request
  if reqMethod req == methodPost
    then insertPaper viewerId
    else respondHtml "paper.edit.html.mustache" PaperNew

{-@ insertPaper :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
insertPaper :: UserId -> Controller ()
insertPaper authorId = do
  params <- parseForm
  let title    = lookup "title" params
  let abstract = lookup "abstract" params
  case (title, abstract) of
    (Just title, Just abstract) -> do
      -- ENFORCE: authorId == viewerId && accepted == false && stage == Submit
      paperId <- insert (Paper authorId title abstract False)
      respondTagged (redirectTo (paperRoute paperId))
    _ -> respondTagged badRequest



------------------------------------------------------------------------------------------------
-- | Misc
------------------------------------------------------------------------------------------------


{-@ getMyPaper :: u:_ -> _ -> TaggedT<{\v -> entityKey v == u}, {\_ -> False}> _ _ @-}
getMyPaper :: UserId -> PaperId -> Controller (Maybe PaperData)
getMyPaper userId paperId = do
  maybePaper <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. userId)
  case maybePaper of
    Nothing    -> return Nothing
    Just paper -> do
      authors           <- getAuthors paper
      reviews           <- if currentStage == PublicStage then getReviews paper else return []
      (title, abstract) <- project2 (paperTitle', paperAbstract') paper
      return . Just $ PaperData paperId title abstract authors reviews


paperRoute :: PaperId -> ByteString
paperRoute paperId = encodeUtf8 (Text.pack path)
 where
  pid  = fromSqlKey paperId
  path = printf "/paper/%d" pid

paperEditRoute :: PaperId -> String
paperEditRoute paperId = printf "/paper/%d/edit" (fromSqlKey paperId)
