{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Controllers where

import           Data.Aeson
import           Data.ByteString                ( ByteString )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , ReaderT(..)
                                                , runReaderT
                                                )
import           Database.Persist.Sqlite        ( SqlBackend )
import qualified Control.Concurrent.MVar       as MVar
import qualified Text.Mustache.Types           as Mustache
import           Frankie.Auth
import           Frankie.Config

import           Binah.Actions
import           Binah.Frankie
import           Binah.Core
import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Templates
import           Concurrent
import qualified Network.AWS                   as AWS
import qualified Network.AWS.S3                as S3
import           Network.Socket                 ( PortNumber )

import           Model

data Config = Config
  { configAuthMethod :: !(AuthMethod (Entity User) Controller)
  , configTemplateCache :: !(MVar.MVar Mustache.TemplateCache)
  , configAWS :: AWSConfig
  , configSMTP :: SMTPConfig
  , configBackend :: SqlBackend
  }

data SMTPConfig = SMTPConfig
  { smtpHost :: String
  , smtpPort :: PortNumber
  , smtpUser :: String
  , smtpPass :: String
  }

data AWSConfig = AWSConfig
  { awsAuth :: AWS.Auth
  , awsRegion:: AWS.Region
  , awsBucket :: S3.BucketName
  }

type Controller = TaggedT (ReaderT SqlBackend (ConfigT Config (ControllerT TIO)))

instance Frankie.Auth.HasAuthMethod (Entity User) Controller Config where
  getAuthMethod = configAuthMethod

instance HasSqlBackend Config where
  getSqlBackend = configBackend

instance HasTemplateCache Config where
  getTemplateCache = configTemplateCache

type Task = TaggedT (ReaderT SqlBackend (ConfigT Config TIO))

runTask :: Task () -> Controller ()
runTask task = do
  b      <- backend
  config <- getConfig
  let t = mapTaggedT (\t -> runReaderT (unConfigT (runReaderT t b)) config) task
  flip mapTaggedT (forkTIO t) $ \m -> do
    liftTIO m
    return ()


--------------------------------------------------------------------------------
-- | Responses
--------------------------------------------------------------------------------

defaultHeaders :: ResponseHeaders
defaultHeaders = [(hContentType, "application/json")]

{-@ respondJSON :: _ -> _ -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ _ @-}
respondJSON :: ToJSON a => Status -> a -> Controller b
respondJSON status a = respondTagged (jsonResponse status a)

jsonResponse :: ToJSON a => Status -> a -> Response
jsonResponse status a = Response status defaultHeaders (encode a)

{-@ respondError :: _ -> _ -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ _ @-}
respondError :: Status -> Maybe String -> Controller a
respondError status error = respondTagged (errorResponse status error)

errorResponse :: Status -> Maybe String -> Response
errorResponse status error = Response status defaultHeaders (encodeError error)
 where
  encodeError Nothing  = encode $ object []
  encodeError (Just e) = encode $ object ["error" .= e]

notFoundJSON :: Response
notFoundJSON = errorResponse status404 Nothing

--------------------------------------------------------------------------------
-- | Misc
--------------------------------------------------------------------------------

hAccessControlAllowOrigin :: HeaderName
hAccessControlAllowOrigin = "Access-Control-Allow-Origin"

-- TODO refine liftTIO
{-@ ignore decodeBody @-}
{-@ decodeBody :: TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ _ @-}
decodeBody :: FromJSON a => Controller a
decodeBody = do
  req  <- request
  body <- liftTIO $ reqBody req
  case eitherDecode body of
    Left  s -> respondError status400 (Just s)
    Right a -> return a

{-@ requireOrganizer ::
  u: _ -> TaggedT<{\_ -> True}, {\v -> v == currentUser}> _ {v: () | IsOrganizer u}
@-}
requireOrganizer :: Entity User -> Controller ()
requireOrganizer user = do
  level <- project userLevel' user
  if level == "organizer" then return () else respondError status403 Nothing

{-@ ignore mapMC @-}
{-@ mapMC :: forall <inn :: Entity User -> Bool, out :: Entity User -> Bool>.
(a -> TaggedT<inn, out> _ b) -> [a] -> TaggedT<inn, out> _ [b]
@-}
mapMC :: MonadTIO m => (a -> TaggedT m b) -> [a] -> TaggedT m [b]
mapMC = mapM

{-@ forMC :: forall <inn :: Entity User -> Bool, out :: Entity User -> Bool>.
[a] -> (a -> TaggedT<inn, out> _ b) -> TaggedT<inn, out> _ [b]
@-}
forMC :: MonadTIO m => [a] -> (a -> TaggedT m b) -> TaggedT m [b]
forMC = flip mapMC
