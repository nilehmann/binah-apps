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
import           Data.Functor                   ( (<&>) )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache
import           Text.Printf                    ( printf )
import           Text.Read                      ( readMaybe )
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


------------------------------------------------------------------------------------------------
-- | Show Paper
------------------------------------------------------------------------------------------------

data PaperShow = PaperShow PaperData [AnonymousReview]

instance TemplateData PaperShow where
  templateFile = "paper.show.html.mustache"

  toMustache (PaperShow paperData reviews) =
    Mustache.object ["paper" ~> paperData, "reviews" ~> reviews]


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
    Just paperData -> respondHtml $ uncurry PaperShow paperData

  paper             <- selectFirstOr404 (paperId' ==. paperId)
  isPC              <- pc viewer
  authors           <- if isPC then getAuthors paper else return []
  reviews           <- if isPC then getReviews paper else return []
  (title, abstract) <- if isPC
    then project2 (paperTitle', paperAbstract') paper
    else if currentStage == "public"
      then do
        accepted <- project paperAccepted' paper
        if accepted then project2 (paperTitle', paperAbstract') paper else return ("", "")
      else return ("", "")

  respondHtml $ PaperShow (PaperData paperId title abstract authors) reviews


------------------------------------------------------------------------------------------------
-- | Edit Paper
------------------------------------------------------------------------------------------------

data PaperEdit = PaperNew | PaperEdit PaperId PaperData

instance TemplateData PaperEdit where
  templateFile = "paper.edit.html.mustache"

  toMustache PaperNew = Mustache.object ["action" ~> ("/paper" :: String)]
  toMustache (PaperEdit id paper) =
    Mustache.object ["action" ~> paperEditRoute id, "paper" ~> paper]


{-@ paperEdit :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperEdit :: Int64 -> Controller ()
paperEdit pid = do
  let paperId = toSqlKey pid
  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  req      <- request
  if reqMethod req == methodPost
    then do
      _ <- updatePaper paperId
      respondTagged (redirectTo (paperRoute paperId))
    else do
      maybePaper <- getMyPaper viewerId paperId
      case maybePaper of
        Nothing             -> respondTagged notFound
        Just (paperData, _) -> respondHtml $ PaperEdit paperId paperData

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
  when (currentStage /= "submit") (respondTagged forbidden)

  viewer   <- requireAuthUser
  viewerId <- project userId' viewer
  req      <- request
  if reqMethod req == methodPost then insertPaper viewerId else respondHtml PaperNew

{-@ insertPaper :: 
     {u:_ | u == entityKey currentUser} 
  -> TaggedT<{\v -> v == currentUser}, {\_ -> True}> _ _ 
@-}
insertPaper :: UserId -> Controller ()
insertPaper authorId = do
  params <- parseForm
  let title    = lookup "title" params
  let abstract = lookup "abstract" params
  case (title, abstract, currentStage == "submit") of
    (Just title, Just abstract, True) -> do
      paperId <- insert (mkPaper authorId title abstract False)
      respondTagged (redirectTo (paperRoute paperId))
    _ -> respondTagged badRequest

------------------------------------------------------------------------------------------------
-- | Show Paper (Chair View)
------------------------------------------------------------------------------------------------

data PaperChair = PaperChair PaperData [UserData] [Text]

instance TemplateData PaperChair where
  templateFile = "paper.chair.html.mustache"

  toMustache (PaperChair paper pcs reviewers) = Mustache.object
    [ "action" ~> ("" :: String)
    , "paper" ~> paper
    , "pcs" ~> pcs
    , "reviews" ~> map toReview reviewers
    ]
    where toReview reviewer = Mustache.object ["reviewer" ~> reviewer]

data UserData = UserData {userDataId :: UserId, userDataName :: Text}

instance ToMustache UserData where
  toMustache (UserData id name) = Mustache.object ["id" ~> id, "name" ~> name]

{-@ paperChair :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
paperChair :: Int64 -> Controller ()
paperChair pid = do
  let paperId = toSqlKey pid
  viewer    <- requireAuthUser
  _         <- checkChairOr forbidden viewer
  viewerId  <- project userId' viewer
  req       <- request
  _         <- if reqMethod req == methodPost then assignReviewer paperId else return ()

  paper     <- getPaper paperId
  -- TODO: we should filter pcs that are already reviewers here
  pcs       <- selectList (userLevel' ==. "pc")
  pcsData   <- projectList2 (userId', userName') pcs
  reviewers <- getReviewers paperId
  respondHtml $ PaperChair paper (map (uncurry UserData) pcsData) reviewers

{-@ assignReviewer :: _ -> TaggedT<{\v -> v == currentUser && IsChair v}, {\_ -> True}> _ _ @-}
assignReviewer :: PaperId -> Controller ()
assignReviewer paperId = do
  params <- parseForm
  let reviewerId = lookup "reviewer" params <&> Text.unpack >>= readMaybe <&> toSqlKey
  case (reviewerId, currentStage == "review") of
    (Just reviewerId, True) -> do
      _ <- selectFirstOr forbidden (userId' ==. reviewerId &&: userLevel' ==. "pc")
      _ <- insert (mkReviewAssignment paperId reviewerId "")
      return ()
    _ -> respondTagged badRequest

{-@ getReviewers :: _ -> TaggedT<{\v -> IsChair v}, {\_ -> False}> _ _ @-}
getReviewers :: PaperId -> Controller [Text]
getReviewers paperId = do
  assignments <- selectList (reviewAssignmentPaper' ==. paperId)
  reviewerIds <- projectList reviewAssignmentUser' assignments
  reviewers   <- selectList (userId' <-. reviewerIds)
  projectList userName' reviewers

------------------------------------------------------------------------------------------------
-- | Helpers
------------------------------------------------------------------------------------------------

{-@ getMyPaper :: u:_ -> _ -> TaggedT<{\v -> entityKey v == u}, {\_ -> False}> _ _ @-}
getMyPaper :: UserId -> PaperId -> Controller (Maybe (PaperData, [AnonymousReview]))
getMyPaper userId paperId = do
  maybePaper <- selectFirst (paperId' ==. paperId &&: paperAuthor' ==. userId)
  case maybePaper of
    Nothing    -> return Nothing
    Just paper -> do
      authors           <- getAuthors paper
      reviews           <- if currentStage == "public" then getReviews paper else return []
      (title, abstract) <- project2 (paperTitle', paperAbstract') paper
      return . Just $ (PaperData paperId title abstract authors, reviews)

{-@ getPaper :: _ -> TaggedT<{\v -> IsPc v}, {\v -> v == currentUser}> _ _ @-}
getPaper :: PaperId -> Controller PaperData
getPaper paperId = do
  paper             <- selectFirstOr404 (paperId' ==. paperId)
  authors           <- getAuthors paper
  (title, abstract) <- project2 (paperTitle', paperAbstract') paper
  return $ (PaperData paperId title abstract authors)


{-@ getReviews ::
  p: _ ->
  TaggedT<{\v -> IsPc v ||
                 (currentStage == "public" && isAuthor (entityKey v) (entityKey p))},
          {\_ -> False}> _ _ @-}
getReviews :: Entity Paper -> Controller [AnonymousReview]
getReviews paper = do
  paperId     <- project paperId' paper
  reviews     <- selectList (reviewPaper' ==. paperId)
  reviewsData <- projectList2 (reviewScore', reviewContent') reviews
  return $ map (uncurry AnonymousReview) reviewsData


{-@ getAuthors :: p: _ -> TaggedT<{\u -> PcOrAuthorOrAccepted p u}, {\_ -> False}> _ _ @-}
getAuthors :: Entity Paper -> Controller [Text]
getAuthors paper = do
  (paperId, authorId) <- project2 (paperId', paperAuthor') paper

  author              <- selectList (userId' ==. authorId)
  authors             <- projectList userName' author

  coauthors           <- selectList (paperCoauthorPaper' ==. paperId)
  coauthorNames       <- projectList paperCoauthorAuthor' coauthors

  return $ authors ++ coauthorNames


paperRoute :: PaperId -> ByteString
paperRoute paperId = encodeUtf8 (Text.pack path)
 where
  pid  = fromSqlKey paperId
  path = printf "/paper/%d" pid


paperEditRoute :: PaperId -> String
paperEditRoute paperId = printf "/paper/%d/edit" (fromSqlKey paperId)

data AnonymousReview = AnonymousReview { reviewDataScore :: Int, reviewDataContent :: Text}

data PaperData = PaperData
  { paperDataId :: PaperId
  , paperDataTitle :: Text
  , paperDataAbstract :: Text
  , paperDataAuthors :: [Text]
  }

instance ToMustache AnonymousReview where
  toMustache (AnonymousReview score content) =
    Mustache.object ["score" ~> score, "content" ~> content]

instance ToMustache PaperData where
  toMustache (PaperData id title abstract authors) =
    Mustache.object ["id" ~> id, "title" ~> title, "abstract" ~> abstract, "authors" ~> authors]
