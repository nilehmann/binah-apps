{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Auth where

import           Control.Monad.Trans.Class      ( lift )
import           Control.Monad.Time             ( MonadTime(..) )
import           Control.Monad.Except           ( runExceptT )
import           Control.Lens.Operators         ( (?~)
                                                , (^.)
                                                , (^?)
                                                , (<&>)
                                                )
import           Control.Lens.Combinators
import           Control.Lens.Lens              ( (&) )
import           Control.Lens.Internal.ByteString
                                                ( unpackLazy8 )
import           Frankie.Auth
import           Crypto.JWT
import           Crypto.JOSE.Types              ( Base64Octets(..) )
import           Data.Text                      ( Text(..) )
import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as T
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as ByteString
import qualified Data.ByteString.Lazy          as L
import           Data.Int                       ( Int64 )
import           Database.Persist.Sql           ( toSqlKey
                                                , fromSqlKey
                                                )
import           GHC.Generics
import           Text.Read                      ( readMaybe )

import           Binah.Core
import           Binah.Actions
import           Binah.Updates
import           Binah.Insert
import           Binah.Filters
import           Binah.Helpers
import           Binah.Infrastructure
import           Binah.Templates
import           Binah.Frankie

import           Controllers
import           Model
import           JSON


---------------------------------------------------------------------------------------------------
-- SignIn Controller
---------------------------------------------------------------------------------------------------

{-@ ignore signIn @-}
signIn :: Controller ()
signIn = do
  (SignInReq username password) <- decodeBody
  user                          <- authUser username password
  userId                        <- project userId' user
  token                         <- genJwt userId
  userRes                       <-
    UserRes username
    <$> project userFullName'     user
    <*> project userAffiliation'  user
    <*> project userEmailAddress' user
    <*> project userLevel'        user

  respondJSON status200
    $ SignInRes { resToken = unpackLazy8 $ encodeCompact token, resUser = userRes }

{-@ ignore genJwt @-}
genJwt :: UserId -> Controller SignedJWT
genJwt userId = do
  claims <- liftTIO $ mkClaims userId
  jwt    <- liftTIO $ doJwtSign claims
  case jwt of
    Right jwt                         -> return jwt
    Left  (JWSError                e) -> respondError status500 (Just (show e))
    Left  (JWTClaimsSetDecodeError s) -> respondError status400 (Just s)
    Left  JWTExpired                  -> respondError status401 (Just "expired token")
    Left  _                           -> respondError status401 Nothing

{-@ ignore authUser @-}
authUser :: Text -> Text -> Controller (Entity User)
authUser username password = do
  maybeUser <- selectFirst (userPassword' ==. password &&: userUsername' ==. username)
  case maybeUser of
    Nothing   -> respondError status401 (Just "incorrect login")
    Just user -> return user

data SignInReq = SignInReq
  { reqUsername :: Text
  , reqPassword :: Text
  }
  deriving Generic

instance FromJSON SignInReq where
  parseJSON = genericParseJSON (stripPrefix "res")

data UserRes = UserRes
  { userUsername :: Text
  , userFullName :: Text
  , userAffiliation :: Text
  , userEmailAddress :: Text
  , userLevel    :: String
  }
  deriving Generic

data SignInRes = SignInRes
  { resToken :: String
  , resUser  :: UserRes
  }
  deriving Generic

instance ToJSON UserRes where
  toEncoding = genericToEncoding (stripPrefix "res")

instance ToJSON SignInRes where
  toEncoding = genericToEncoding (stripPrefix "res")


---------------------------------------------------------------------------------------------------
-- Auth method
---------------------------------------------------------------------------------------------------

authMethod :: AuthMethod (Entity User) Controller
authMethod = AuthMethod
  { authMethodTry     = checkIfAuth
  , authMethodRequire = checkIfAuth >>= \case
                          Just user -> pure user
                          Nothing   -> respondError status401 Nothing
  }

{-@ ignore checkIfAuth @-}
checkIfAuth :: Controller (Maybe (Entity User))
checkIfAuth = do
  authHeader <- requestHeader hAuthorization
  let token = authHeader >>= ByteString.stripPrefix "Bearer " <&> L.fromStrict
  claims <- liftTIO $ mapM doVerify token
  case claims of
    Just (Right claims) -> do
      let sub    = claims ^. claimSub ^? _Just . string
      let userId = sub <&> T.unpack >>= readMaybe <&> toSqlKey
      case userId of
        Nothing     -> return Nothing
        Just userId -> selectFirst (userId' ==. userId)
    _ -> return Nothing

---------------------------------------------------------------------------------------------------
-- JWT
---------------------------------------------------------------------------------------------------

mkClaims :: UserId -> TIO ClaimsSet
mkClaims userId = do
  t <- currentTime
  return $ emptyClaimsSet & (claimSub ?~ uid ^. re string) & (claimIat ?~ NumericDate t)
  where uid = T.pack (show (fromSqlKey userId))

doJwtSign :: ClaimsSet -> TIO (Either JWTError SignedJWT)
doJwtSign claims = runExceptT $ do
  alg <- bestJWSAlg key
  signClaims key (newJWSHeader ((), alg)) claims

doVerify :: L.ByteString -> TIO (Either JWTError ClaimsSet)
doVerify s = runExceptT $ do
  let audCheck = const True
  s' <- decodeCompact s
  verifyClaims (defaultJWTValidationSettings audCheck) key s'

-- TODO: Read this from env
key :: JWK
key = fromOctets raw
 where
  raw :: ByteString
  raw = "\xe5L\xb7\xf6\x03|\xb6\n\x10\xd8\xb8\x96\xe2\xc4W@#W\xb4>\th*iiW\x12\x80z\x04i="

instance MonadRandom TIO where
  getRandomBytes x = TIO (getRandomBytes x)

instance MonadTime TIO where
  currentTime = TIO currentTime
