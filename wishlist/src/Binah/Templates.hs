{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, AllowAmbiguousTypes #-}

module Binah.Templates
  ( HasTemplateCache(..)
  , renderTemplate
  )
where

import           Frankie.Config
import qualified Text.Mustache.Types           as Mustache
import qualified Data.HashMap.Strict           as HashMap
import qualified Text.Mustache                 as Mustache
import           Data.Text                      ( Text )
import           Control.Concurrent.MVar        ( MVar
                                                , readMVar
                                                , modifyMVar_
                                                )
import           Control.Exception              ( evaluate )

import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Frankie

import           Model

class HasTemplateCache config where
  getTemplateCache :: config -> MVar Mustache.TemplateCache

{-@ ignore getOrLoadTemplate @-}
getOrLoadTemplate
  :: (MonadConfig config m, MonadTIO m, HasTemplateCache config)
  => [FilePath]
  -> FilePath
  -> m Mustache.Template
getOrLoadTemplate searchDirs file = do
  cacheMVar <- getTemplateCache <$> getConfig
  oldCache  <- liftTIO $ TIO (readMVar cacheMVar)
  case HashMap.lookup file oldCache of
    Just template -> pure template
    Nothing -> liftTIO $ TIO $ Mustache.compileTemplateWithCache searchDirs oldCache file >>= \case
      Right template ->
        let updatedCache =
                HashMap.insert (Mustache.name template) template (Mustache.partials template)
        in  do
              modifyMVar_ cacheMVar (\currentCache -> evaluate $ currentCache <> updatedCache)
              pure template
      Left err -> error $ "Error parsing template " ++ file ++ ": " ++ show err

{-@ assume renderTemplate :: _ -> _ -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
{-@ ignore renderTemplate @-}
renderTemplate
  :: forall d w m config
   . ( MonadController w m
     , MonadTIO m
     , MonadConfig config m
     , Mustache.ToMustache d
     , HasTemplateCache config
     )
  => FilePath
  -> d
  -> TaggedT m Text
renderTemplate path templateData = do
  template <- getOrLoadTemplate searchDirs path
  pure $ Mustache.substitute template templateData
  where searchDirs = ["templates"]
