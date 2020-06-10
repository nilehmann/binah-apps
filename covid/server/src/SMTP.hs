module SMTP
  ( renderAndSend
  , renderSendMail
  , simpleMail'
  , simpleMail
  , mkPublicAddress
  , connectSMTP
  , connectSMTP'
  , login
  , Mail
  , Address
  )
where

import qualified Network.Mail.SMTP             as M
import qualified Network.Mail.Mime             as M
                                         hiding ( simpleMail )
import           Network.Socket                 ( PortNumber )
import qualified Data.Text                     as T
import qualified Data.Text.Lazy                as LT
import qualified Data.ByteString               as BS

import           Binah.Infrastructure
import           Binah.Core
import           Binah.Actions
import           Model


-- TODO: LIQUID TYPES

newtype Mail = Mail M.Mail

newtype Address = Address M.Address

mkPublicAddress :: Maybe T.Text -> T.Text -> Address
mkPublicAddress name email = Address (M.Address name email)

simpleMail' :: Address -> Address -> T.Text -> LT.Text -> Mail
simpleMail' (Address from) (Address to) subject body = Mail $ M.simpleMail' from to subject body

simpleMail :: Address -> [Address] -> [Address] -> [Address] -> T.Text -> [M.Part] -> Mail
simpleMail (Address from) to cc bcc subject parts = Mail
  $ M.simpleMail from to' cc' bcc' subject parts
 where
  to'  = map (\(Address a) -> a) to
  cc'  = map (\(Address a) -> a) cc
  bcc' = map (\(Address a) -> a) bcc

login :: MonadTIO m => M.SMTPConnection -> String -> String -> m (M.ReplyCode, BS.ByteString)
login conn user pass = liftTIO $ TIO $ M.login conn user pass

connectSMTP :: MonadTIO m => String -> TaggedT m M.SMTPConnection
connectSMTP hostname = liftTIO $ TIO $ M.connectSMTP hostname

connectSMTP' :: MonadTIO m => String -> PortNumber -> m M.SMTPConnection
connectSMTP' hostname port = liftTIO $ TIO $ M.connectSMTP' hostname port

renderAndSend :: MonadTIO m => M.SMTPConnection -> Mail -> m ()
renderAndSend conn (Mail mail) = liftTIO $ TIO $ M.renderAndSend conn mail

renderSendMail :: MonadTIO m => Mail -> TaggedT m ()
renderSendMail (Mail mail) = liftTIO $ TIO $ M.renderSendMail mail
