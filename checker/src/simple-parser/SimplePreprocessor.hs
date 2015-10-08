{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module SimplePreprocessor (runPreprocessor) where

import Language.Preprocessor.Cpphs
import Control.Monad.IO.Class

options = CpphsOptions { infiles = []
                       , outfiles = []
                       , defines = []
                       , includes = []
                       , preInclude = []
                       , boolopts = BoolOptions { macros = True
                                                , locations = False
                                                , hashline = True
                                                , pragma = False
                                                , stripEol = True
                                                , stripC89 = False
                                                , lang = True
                                                , ansi = False
                                                , layout = True
                                                , literate = False
                                                , warnings = True}
                       }

runPreprocessor    :: MonadIO m => String -> m String
runPreprocessor str = liftIO (runCpphs options "" str)
