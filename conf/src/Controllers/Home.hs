module Controllers.Home where

import           Text.Mustache                 ( ToMustache(..) )
import qualified Text.Mustache.Types           as Mustache
import           Frankie

import           Binah.Templates
import           Binah.Filters
import           Binah.Frankie
import           Controllers

data Home = Home

instance TemplateData Home where
  templateFile = "home.html.mustache"

instance ToMustache Home where
  toMustache Home = Mustache.object []

home :: Controller ()
home = respondHtml Home
