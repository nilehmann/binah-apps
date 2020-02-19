module Controllers.Home where

-- I get a liquid haskell error if I don't import this
import           Data.Int                       ( Int64 )
import           Text.Mustache                  ( (~>)
                                                , ToMustache(..)
                                                )
import qualified Text.Mustache.Types           as Mustache

import           Binah.Core
import           Binah.Actions
import           Binah.Infrastructure
import           Binah.Templates

import           Controllers

data Home = Home

instance TemplateData Home where
  templateFile = "home.html.mustache"

instance ToMustache Home where
  toMustache Home = Mustache.object []

home :: Controller ()
home = respondHtml Home
